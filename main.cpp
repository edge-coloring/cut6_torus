#include <iostream>
#include <string>
#include <vector>
#include <boost/program_options.hpp>
#include <spdlog/spdlog.h>
#include "check.hpp"

using std::vector;
using std::string;

int main(const int ac, const char* const* const av) {
    using namespace boost::program_options;
    options_description description("Options");
    description.add_options()
        ("conf,c", value<string>(), "A configuration file")
        ("edgeids,e", value<vector<int>>()->multitoken(), "A list of contraction edge ids (in dual form)")
        ("help,H", "Display options")
        ("verbosity,v", value<int>()->default_value(0), "1 for debug, 2 for trace");

    variables_map vm;
    store(parse_command_line(ac, av, description), vm);
    notify(vm);

    if (vm.count("help")) {
        description.print(std::cout);
        return 0;
    }
    if (vm.count("verbosity")) {
        auto v = vm["verbosity"].as<int>();
        if (v == 1) {
            spdlog::set_level(spdlog::level::debug);
        }
        if (v == 2) {
            spdlog::set_level(spdlog::level::trace);
        }
    }
    if (vm.count("conf") && vm.count("edgeids")) {
        string conf_file_name = vm["conf"].as<string>();
        vector<int> edgeids = vm["edgeids"].as<vector<int>>();
        check(conf_file_name, edgeids);
    }
    
    return 0;
}