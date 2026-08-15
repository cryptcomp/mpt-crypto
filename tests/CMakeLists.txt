# Enable CTest
enable_testing()

# --------------------------------------------------------------------
# Helper function for defining MPT tests
#   - add_executable
#   - target_link_libraries
#   - add_test
#
# Usage:
#   add_mpt_test(test_name source.c DEPENDENCIES lib1 lib2 ...)
# --------------------------------------------------------------------
function(add_mpt_test TEST_NAME TEST_SOURCE)
    set(options "")
    set(oneValueArgs "")
    set(multiValueArgs DEPENDENCIES)

    cmake_parse_arguments(
        ARG
        "${options}"
        "${oneValueArgs}"
        "${multiValueArgs}"
        ${ARGN}
    )

    # Static variant: links the static `mpt-crypto` target.
    add_executable(${TEST_NAME} ${TEST_SOURCE})
    target_link_libraries(${TEST_NAME} PRIVATE ${ARG_DEPENDENCIES})
    add_test(NAME ${TEST_NAME} COMMAND ${TEST_NAME})

    # Shared variant: when the shared library is also built (MPT_CRYPTO_BUILD_SHARED),
    # run the SAME test against it, so both link forms are exercised by ctest.
    # Swap the static `mpt-crypto` dep for `mpt-crypto-shared`; keep the rest.
    if(MPT_CRYPTO_BUILD_SHARED AND TARGET mpt-crypto-shared)
        set(_shared_deps "")
        foreach(_dep IN LISTS ARG_DEPENDENCIES)
            if(_dep STREQUAL "mpt-crypto")
                list(APPEND _shared_deps mpt-crypto-shared)
            else()
                list(APPEND _shared_deps ${_dep})
            endif()
        endforeach()
        add_executable(${TEST_NAME}_shared ${TEST_SOURCE})
        target_link_libraries(${TEST_NAME}_shared PRIVATE ${_shared_deps})
        add_test(NAME ${TEST_NAME}_shared COMMAND ${TEST_NAME}_shared)

        # Windows has no rpath, so the shared-variant .exe can't find the DLL
        # (which lives in the shared/ output dir) at runtime — it would abort
        # with STATUS_DLL_NOT_FOUND (0xC0000135). Copy mpt-crypto.dll next to the
        # test executable. On ELF/Mach-O the build rpath already handles this.
        if(WIN32)
            add_custom_command(
                TARGET ${TEST_NAME}_shared
                POST_BUILD
                COMMAND
                    ${CMAKE_COMMAND} -E copy_if_different
                    $<TARGET_FILE:mpt-crypto-shared>
                    $<TARGET_FILE_DIR:${TEST_NAME}_shared>
                VERBATIM
            )
        endif()
    endif()
endfunction()

# --------------------------------------------------------------------
# Test definitions
# --------------------------------------------------------------------

add_mpt_test(test_elgamal test_elgamal.c DEPENDENCIES mpt-crypto)

add_mpt_test(
    test_elgamal_verify
    test_elgamal_verify.c
    DEPENDENCIES mpt-crypto secp256k1::secp256k1
)

add_mpt_test(
    test_pok_sk
    test_pok_sk.c
    DEPENDENCIES mpt-crypto secp256k1::secp256k1
)

add_mpt_test(
    test_commitments
    test_commitments.c
    DEPENDENCIES mpt-crypto secp256k1::secp256k1
)

add_mpt_test(test_ipa test_ipa.c DEPENDENCIES mpt-crypto secp256k1::secp256k1)
add_mpt_test(test_ipa_3w test_ipa_3w.c DEPENDENCIES mpt-crypto secp256k1::secp256k1)

add_mpt_test(
    test_bulletproof_agg
    test_bulletproof_agg.c
    DEPENDENCIES mpt-crypto secp256k1::secp256k1
)

add_mpt_test(
    test_bulletproof_agg_hybrid_v1
    test_bulletproof_agg_hybrid_v1.c
    DEPENDENCIES mpt-crypto secp256k1::secp256k1
)

add_mpt_test(
    test_mpt_utility
    test_mpt_utility.cpp
    DEPENDENCIES mpt-crypto secp256k1::secp256k1 OpenSSL::Crypto
)

add_mpt_test(
    test_compact_standard
    test_compact_standard.c
    DEPENDENCIES mpt-crypto secp256k1::secp256k1
)

add_mpt_test(
    test_compact_clawback
    test_compact_clawback.c
    DEPENDENCIES mpt-crypto secp256k1::secp256k1
)

add_mpt_test(
    test_compact_convertback
    test_compact_convertback.c
    DEPENDENCIES mpt-crypto secp256k1::secp256k1
)

add_mpt_test(
    test_ct_tweak_mul
    test_ct_tweak_mul.c
    DEPENDENCIES mpt-crypto secp256k1::secp256k1 OpenSSL::Crypto
)

# IPA microbenchmark. Build manually; do not register with CTest.
add_executable(benchmark_ipa_3w benchmark_ipa_3w.c)

target_link_libraries(
  benchmark_ipa_3w
  PRIVATE
    mpt-crypto
    secp256k1::secp256k1
)

add_mpt_test(
    test_ipa_3w_et
    test_ipa_3w_et.c
    DEPENDENCIES mpt-crypto secp256k1::secp256k1
)

# 3W early-termination microbenchmark. Build manually; do not register with CTest.
add_executable(benchmark_ipa_3w_et benchmark_ipa_3w_et.c)
target_link_libraries(
  benchmark_ipa_3w_et
  PRIVATE
    mpt-crypto
    secp256k1::secp256k1
)

add_mpt_test(
    test_ipa_2w_dynamic
    test_ipa_2w_dynamic.c
    DEPENDENCIES mpt-crypto secp256k1::secp256k1
)

# Dynamic-2W comparison microbenchmark. Build manually; do not register with CTest.
add_executable(benchmark_ipa_2w_dynamic benchmark_ipa_2w_dynamic.c)
target_link_libraries(
  benchmark_ipa_2w_dynamic
  PRIVATE
    mpt-crypto
    secp256k1::secp256k1
)

add_mpt_test(
    test_ipa_2w_dynamic_fast
    test_ipa_2w_dynamic_fast.c
    DEPENDENCIES mpt-crypto secp256k1::secp256k1
)

# Optimized dynamic-2W verifier benchmark. Build manually; do not register with CTest.
add_executable(benchmark_ipa_2w_dynamic_fast benchmark_ipa_2w_dynamic_fast.c)
target_link_libraries(
  benchmark_ipa_2w_dynamic_fast
  PRIVATE
    mpt-crypto
    secp256k1::secp256k1
)

add_mpt_test(
    test_ipa_3w_fast
    test_ipa_3w_fast.c
    DEPENDENCIES mpt-crypto secp256k1::secp256k1
)

# Optimized 3W verifier comparison benchmark. Build manually; do not register with CTest.
add_executable(benchmark_ipa_3w_fast benchmark_ipa_3w_fast.c)
target_link_libraries(
  benchmark_ipa_3w_fast
  PRIVATE
    mpt-crypto
    secp256k1::secp256k1
)

add_mpt_test(
    test_ipa_hybrid_v1
    test_ipa_hybrid_v1.c
    DEPENDENCIES mpt-crypto secp256k1::secp256k1
)

add_mpt_test(
    test_ipa_hybrid_v1_fast
    test_ipa_hybrid_v1_fast.c
    DEPENDENCIES mpt-crypto secp256k1::secp256k1
)

# Hybrid-v1 schedule/Pareto benchmark. Build manually; not a CTest.
add_executable(benchmark_ipa_hybrid_v1 benchmark_ipa_hybrid_v1.c)
target_link_libraries(
  benchmark_ipa_hybrid_v1
  PRIVATE
    mpt-crypto
    secp256k1::secp256k1
)

# Full aggregated Bulletproof Hybrid-v1 end-to-end benchmark.
# Build manually; do not register with CTest.
add_executable(
  benchmark_bulletproof_agg_hybrid_v1
  benchmark_bulletproof_agg_hybrid_v1.c
)
target_link_libraries(
  benchmark_bulletproof_agg_hybrid_v1
  PRIVATE
    mpt-crypto
    secp256k1::secp256k1
)
