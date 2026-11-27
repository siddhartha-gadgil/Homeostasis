import LeanTheory
import Lean.Util.CollectAxioms

/-! Audit all declarations owned by project modules, including definitions and generated
lemmas. The only allowed logical axioms are Lean's standard classical foundations.
This fails on sorryAx, native_decide trust, or any added project/model axiom. -/
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut checked : Nat := 0
  for (name, _) in env.constants.toList do
    let owned := match env.getModuleIdxFor? name with
      | some idx => (`LeanTheory).isPrefixOf env.allImportedModuleNames[idx.toNat]!
      | none => false
    if owned then
      let axioms ← collectAxioms name
      for ax in axioms do
        unless allowed.contains ax do
          throwError "Unexpected axiom {ax} in {name}"
      checked := checked + 1
  if checked == 0 then
    throwError "No project declarations found: audit did not run"
  logInfo m!"Axiom audit passed for {checked} LeanTheory declarations."

#print axioms LeanTheory.Certificates.BlockCertificate.sound
#print axioms LeanTheory.Certificates.local_fixedPoint
#print axioms LeanTheory.Stability.suydamForm_coercive
#print axioms LeanTheory.Stability.suydam_necessary
#print axioms LeanTheory.Stability.hardy_sharp
#print axioms LeanTheory.Stability.picone_certificate
#print axioms LeanTheory.Stability.suydam_from_picone
#print axioms LeanTheory.Certificates.QPoly.checkOn_sound
#print axioms LeanTheory.Certificates.QPoly.riccati_poly_certificate
#print axioms LeanTheory.Certificates.QPoly.example_beyond_constant
#print axioms LeanTheory.Theory.KAM.kam_sequence
#print axioms LeanTheory.Theory.KAM.norm_sub_interp_le
#print axioms LeanTheory.Theory.KAM.PQG.valid_of_nodesOK
#print axioms LeanTheory.Fields.lieBracket_gradient
#print axioms LeanTheory.Fields.lieBracket_gradient_of_contDiffAt
#print axioms LeanTheory.Fields.lieBracket_gradient_of_killing
#print axioms LeanTheory.Sanity.quasisymmetry_not_pde_symmetry
#print axioms LeanTheory.Sanity.qs_lieBracket_X_gradP
#print axioms LeanTheory.Sanity.qs_strain_term
#print axioms LeanTheory.Stability.riccati_le_initial
#print axioms LeanTheory.Stability.riccati_exp_decay
#print axioms LeanTheory.Stability.riccati_hyp_exp
#print axioms ConcLean.SubsetSum.subsetSum_correct
#print axioms LeanTheory.Example.energy_conserved
#print axioms LeanTheory.Example.not_oscillatorLaw_exp
#print axioms LeanTheory.Example.cos_energy
#print axioms LeanTheory.Example.free_velocity_const
#print axioms LeanTheory.Example.amplitude_bound
#print axioms LeanTheory.Example.initialStates_energy_le
#print axioms LeanTheory.Example.amplitude_cert
#print axioms LeanTheory.Fields.curl_fderiv_smul
#print axioms LeanTheory.Fields.invariantBarrier_forward
#print axioms LeanTheory.Fields.ODEGlobal.existsUnique_global
#print axioms LeanTheory.Certificates.EvalCert.ECert.sound
#print axioms LeanTheory.Certificates.KronProof.kernelFact_fixture
#print axioms LeanTheory.CRN.ReactionNetwork.deficiency_nonneg
#print axioms LeanTheory.CRN.ReactionNetwork.numLinkageClasses_eq_of_labelling
#print axioms LeanTheory.CRN.ReactionNetwork.deficiency_relabelSpecies
#print axioms LeanTheory.CRN.Sanity.acrNet_deficiency
#print axioms LeanTheory.CRN.Sanity.emptyNet_deficiency
#print axioms LeanTheory.CRN.ReactionNetwork.MassActionTrajectory.isPos
#print axioms LeanTheory.CRN.ReactionNetwork.MassActionTrajectory.sub_mem_stoichSubspace
#print axioms LeanTheory.CRN.ReactionNetwork.MassActionTrajectory.dotProduct_eq
#print axioms LeanTheory.CRN.Sanity.isoTraj_trajectory
#print axioms LeanTheory.CRN.Sanity.acrNet_steadyState_xA
#print axioms LeanTheory.CRN.ReactionNetwork.HasACR.hasDerivAt_zero
#print axioms LeanTheory.CRN.HasPerfectAdaptation.infinitesimalHomeostasis
#print axioms LeanTheory.CRN.hasPerfectAdaptation_iff_error_zero
#print axioms LeanTheory.CRN.Sanity.acrNet_hasACRNonvacuous
#print axioms LeanTheory.CRN.Sanity.quad_not_perfectAdaptation
#print axioms LeanTheory.CRN.ReactionNetwork.IsAntitheticController.dotProduct_field
#print axioms LeanTheory.CRN.ReactionNetwork.IsAntitheticController.hasPerfectAdaptation
#print axioms LeanTheory.CRN.Design.aifNet_hasPerfectAdaptation
#print axioms LeanTheory.CRN.Design.aifNet_dilution_breaks_setpoint
#print axioms LeanTheory.CRN.ReactionNetwork.generator_linear
#print axioms LeanTheory.CRN.ReactionNetwork.isClosedSet_zero_of_src
#print axioms LeanTheory.CRN.ReactionNetwork.IsAntitheticController.stationary_mean
#print axioms LeanTheory.CRN.Sanity.bdNet_poisson_isStationary
#print axioms LeanTheory.CRN.Sanity.acrNet_reaches_extinction
#print axioms LeanTheory.CRN.Design.aifNet_stationary_mean
#print axioms LeanTheory.CRN.Sanity.bdNet_poisson_isStationaryDistribution
#print axioms LeanTheory.Homeostasis.infinitesimalHomeostasis_iff_det
#print axioms LeanTheory.Homeostasis.massAction_infinitesimalHomeostasis_iff_det
#print axioms LeanTheory.Homeostasis.Sanity.ffl_homeostatic
#print axioms LeanTheory.Homeostasis.Sanity.cascade_not_homeostatic
#print axioms LeanTheory.CRN.ReactionNetwork.hasACR_of_cofactor
#print axioms LeanTheory.CRN.ReactionNetwork.not_isPosSteadyState_of_posComb
#print axioms LeanTheory.Certificates.Poly.psatz_empty
#print axioms LeanTheory.CRN.Sanity.acrNet_hasACR_cert
#print axioms LeanTheory.CRN.Generated.acrToyGenNet_hasACR
#print axioms LeanTheory.CRN.Generated.aifGenNet_hasACR
#print axioms LeanTheory.CRN.ReactionNetwork.stationary_moment_le
#print axioms LeanTheory.CRN.ReactionNetwork.hasDrift_of_cert
#print axioms LeanTheory.CRN.Sanity.bd_poisson_attains_bound
#print axioms LeanTheory.CRN.Sanity.bd_second_moment_le
#print axioms LeanTheory.Markov.tendsto_outMass
#print axioms LeanTheory.Markov.isStochastic_uniformize
#print axioms LeanTheory.CRN.ReactionNetwork.tendsto_outMass_cme
#print axioms LeanTheory.CRN.ReactionNetwork.isGenStationaryFor_of_vecMul_eq_zero
#print axioms LeanTheory.CRN.Sanity.acrNet_extinction
