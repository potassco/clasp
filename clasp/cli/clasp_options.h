//
// Copyright (c) 2006-present Benjamin Kaufmann
//
// This file is part of Clasp. See https://potassco.org/clasp/
//
// Permission is hereby granted, free of charge, to any person obtaining a copy
// of this software and associated documentation files (the "Software"), to
// deal in the Software without restriction, including without limitation the
// rights to use, copy, modify, merge, publish, distribute, sublicense, and/or
// sell copies of the Software, and to permit persons to whom the Software is
// furnished to do so, subject to the following conditions:
//
// The above copyright notice and this permission notice shall be included in
// all copies or substantial portions of the Software.
//
// THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
// IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
// FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
// AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
// LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
// FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS
// IN THE SOFTWARE.
//
#pragma once

#include <clasp/clasp_facade.h>
#include <string>

namespace Potassco::ProgramOptions {
class OptionContext;
class OptionGroup;
class ParsedOptions;
} // namespace Potassco::ProgramOptions

/*!
 * \file
 * \brief Types and functions for processing command-line options.
 */
//! Namespace for types and functions used by the command-line interface.
namespace Clasp::Cli {

/**
 * \defgroup cli Cli
 * \brief Types mainly relevant to the command-line interface.
 * \ingroup facade
 * @{
 */

class ClaspCliConfig;
//! Class for iterating over a set of configurations.
class ConfigIter {
public:
    [[nodiscard]] auto name() const -> const char*;
    [[nodiscard]] auto base() const -> const char*;
    [[nodiscard]] auto args() const -> const char*;
    [[nodiscard]] bool valid() const;
    bool               next();

private:
    friend class ClaspCliConfig;
    ConfigIter(const char* x);
    const char* base_;
};
//! Valid configuration keys.
/*!
 * \see clasp_cli_configs.inl
 */
enum ConfigKey {
#define CONFIG(id, k, c, s, p)    config_##k,
#define CLASP_CLI_DEFAULT_CONFIGS config_default = 0,
#define CLASP_CLI_AUX_CONFIGS     config_default_max_value,
#include <clasp/cli/clasp_cli_configs.inl>

    config_aux_max_value,
    config_many, // default portfolio
    config_max_value,
    config_asp_default    = config_tweety,
    config_sat_default    = config_trendy,
    config_tester_default = config_tester,
};
/*!
 * \brief Class for storing/processing command-line options.
 *
 * Caveats when using incrementally, e.g., from clingo:
 * - `supp-models`: State Transition between `yes` and `no` is not supported.
 *     - Setting `supp-models` to `yes` is irreversible for a step
 *       because it enables possibly destructive simplifications
 *       and skips SCC-checking (i.e., new SCCs are silently discarded).
 *     - Nogoods learnt during supp-models=no are not tagged and
 *       hence can't simply be removed on transition to yes.
 * - stats: Statistics level can only be increased.
 *     - A level once activated stays activated even if it is subsequently decreased via option.
 * - Save-progress, sign-fix, opt-heuristic: No unset of previously set values.
 *     - Once set, signs are only unset if forgetOnStep includes sign.
 * - no-lookback: State Transition (yes<->no) not supported.
 *     - noLookback=yes is a destructive meta-option that disables lookback-options by changing their value
 *     - noLookback=no does not re-enable those options.
 */
class ClaspCliConfig : public ClaspConfig {
public:
    //! Returns defaults for the given problem type.
    static auto getDefaults(ProblemType f) -> const char*;
    //! Returns the configuration with the given key.
    static auto getConfig(ConfigKey key) -> ConfigIter;
    //! Returns the ConfigKey of k or -1 if k is not a known configuration.
    static int getConfigKey(std::string_view k);

    ClaspCliConfig();
    ~ClaspCliConfig() override;
    // Base interface
    void prepare(SharedContext&) override;
    void reset() override;
    auto config(const char*) -> Configuration* override;

    /*!
     * \name Key-based low-level interface
     *
     * The functions in this group do not throw exceptions but
     * signal logic errors via return values < 0.
     * @{ */

    using KeyType = uint32_t;
    static const KeyType key_invalid; //!< Invalid key used to signal errors.
    static const KeyType key_root;    //!< Root key of a configuration, i.e. "."
    static const KeyType key_tester;  //!< Root key for tester options, i.e. "tester."
    static const KeyType key_solver;  //!< Root key for (array of) solver options, i.e. "solver."

    //! Returns true if k is a leaf, i.e., has no subkeys.
    static bool isLeafKey(KeyType k);

    //! Retrieves a handle to the specified key.
    /*!
     * \param key   A valid handle to a key.
     * \param name  The name of the subkey to retrieve.
     * \return
     *   - `key` if `name` is empty.
     *   - `key_invalid` if `name` is not a subkey of `key`.
     *   - A handle to the specified subkey otherwise.
     */
    [[nodiscard]] auto getKey(KeyType key, std::string_view name) const -> KeyType;

    //! Retrieves a handle to the specified element of the given array key.
    /*!
     * \param arr     A valid handle to an array.
     * \param element The index of the element to retrieve.
     * \return
     *   - A handle to the requested element, or
     *   - `key_invalid`, if `arr` does not reference an array or `element` is out of bounds.
     */
    [[nodiscard]] auto getArrKey(KeyType arr, uint32_t element) const -> KeyType;

    //! Retrieves information about the specified key.
    /*!
     * \param key           A valid handle to a key.
     * \param[out] nSubkeys The number of subkeys for this key, or 0 if the key is a leaf node.
     * \param[out] arrLen   If the key is an array, the length of the array (can be 0); otherwise, -1.
     * \param[out] help     A description of the key.
     * \param[out] nValues  The number of values the key currently has (0 or 1), or -1 if it cannot have values.
     * \note All out parameters are optional (i.e., can be null).
     * \return The number of output values written, or -1 if the key is invalid.
     */
    int getKeyInfo(KeyType key, int* nSubkeys = nullptr, int* arrLen = nullptr, std::string* help = nullptr,
                   int* nValues = nullptr) const;

    //! Returns the name of the `i-th` subkey of `k` or and empty view if no such subkey exists.
    [[nodiscard]] auto getSubkey(KeyType k, uint32_t i) const -> std::string_view;

    //! Creates and returns a string representation of the value of the given key.
    /*!
     * \param key        A valid handle to a key.
     * \param[out] value The current value of the key.
     * \return The length of `value`, or a negative value if `key` either has no value (-1), or an error occurred
     *         while writing the value (< -1).
     */
    int getValue(KeyType key, std::string& value) const;

    //! Sets the option identified by the given key.
    /*!
     * \param key A valid handle to a key.
     * \param value The value to set.
     * \return
     *   - > 0: if the value was set.
     *   - = 0: if value is not a valid value for the given key.
     *   - < 0: if the key does not accept a value (-1), or an error occurred (< -1).
     */
    int setValue(KeyType key, std::string_view value);

    //@}

    /*!
     * \name String-based interface
     *
     * The functions in this group wrap the key-based functions and
     * signal logic errors by throwing exceptions.
     * @{ */
    //! Returns the value of the option identified by the given path.
    [[nodiscard]] auto getValue(std::string_view path) const -> std::string;
    //! Returns true if the given path has an associated value.
    [[nodiscard]] bool hasValue(std::string_view path) const;
    //! Sets the option identified by the given path.
    bool setValue(std::string_view path, std::string_view value);
    //@}

    //! Validates this configuration.
    bool validate();

    /*!
     * \name App interface
     *
     * Functions for connecting a configuration with the ProgramOptions library.
     * @{ */
    //! Adds all available options to root.
    /*!
     * Once options are added, root can be used with an option source (e.g., the command-line)
     * to populate this object.
     */
    void addOptions(Potassco::ProgramOptions::OptionContext& root);
    //! Adds options that are disabled by the options contained in 'parsed' to 'parsed'.
    void addDisabled(Potassco::ProgramOptions::ParsedOptions& parsed);
    //! Applies the options in parsed and finalizes and validates this configuration.
    bool finalize(const Potassco::ProgramOptions::ParsedOptions& parsed, ProblemType type, bool applyDefaults);

    //! Populates this configuration with the options given in `args` and finalizes it.
    /*!
     * \param args options in argv format.
     * \param t Problem type for which this configuration is created. Used to set defaults.
     */
    bool setConfig(std::span<const char*> args, ProblemType t);

    //! Releases internal option objects needed for command-line style option processing.
    /*!
     * \note Calls to certain functions of this object (e.g., addOptions(), setConfig())
     *       recreate the option objects if necessary.
     */
    void releaseOptions();
    //@}
private:
    struct ParseContext;
    using OptionContext = Potassco::ProgramOptions::OptionContext;
    using Options       = Potassco::ProgramOptions::OptionGroup;
    using OptionsPtr    = std::unique_ptr<Options>;
    using ParsedOpts    = Potassco::ProgramOptions::ParsedOptions;
    // Operations on active config and solver
    int setOption(int option, uint8_t setMode, uint32_t sId, std::string_view value);
    // App interface impl
    int  setAppOpt(int o, uint8_t mode, std::string_view value);
    bool setAppDefaults(ConfigKey config, uint8_t mode, const ParsedOpts& exclude, ProblemType t);
    bool finalizeAppConfig(uint8_t mode, const ParsedOpts& exclude, ProblemType t, bool defs);
    auto finalizeParsed(uint8_t mode, const ParsedOpts& parsed, ParsedOpts& exclude) const -> const ParsedOpts&;
    void createOptions();
    bool setCliOption(std::string_view name, int option, std::string_view value);
    bool assignDefaults(const ParsedOpts&);
    [[nodiscard]] auto getOptionName(int key) const -> std::string_view;

    // Configurations
    auto getConfig(uint8_t key, std::string& tempMem) const -> ConfigIter;
    bool setConfig(const char* name, std::string_view args, uint8_t mode, uint32_t sId, const ParsedOpts& exclude,
                   ParsedOpts* out);
    bool setConfig(const ConfigIter& c, uint8_t mode, uint32_t sId, const ParsedOpts& exclude, ParsedOpts* out);
    // helpers
    OptionsPtr    opts_;
    ParseContext* parseCtx_;
    std::string   config_[2];
    bool          validate_;
};
//! Validates the given solver configuration and returns an error string if invalid.
auto validate(const SolverParams& solver, const SolveParams& search) -> const char*;
//@}

} // namespace Clasp::Cli
