/-
Copyright (c) 2026 LeanTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanTheory contributors
-/
module

public import LeanTheory.Bridge.CRNCertificates
public import LeanTheory.Bridge.Example
public import LeanTheory.Certificates.BlockBounds
public import LeanTheory.Certificates.BoolCert
public import LeanTheory.Certificates.Contraction
public import LeanTheory.Certificates.ConvAlgebra
public import LeanTheory.Certificates.DigitSumCert
public import LeanTheory.Certificates.DiscreteMaxPrinciple
public import LeanTheory.Certificates.EvalCert
public import LeanTheory.Certificates.EvalCertFIv
public import LeanTheory.Certificates.Example
public import LeanTheory.Certificates.FamPackCert
public import LeanTheory.Certificates.FourierRegularity
public import LeanTheory.Certificates.Generated.AcrToyGen
public import LeanTheory.Certificates.Generated.AifGen
public import LeanTheory.Certificates.Generated.EnvZOmpRGen
public import LeanTheory.Certificates.IccListCert
public import LeanTheory.Certificates.LyapunovCert
public import LeanTheory.Certificates.KernelFact
public import LeanTheory.Certificates.KronBall
public import LeanTheory.Certificates.KronBallCheb
public import LeanTheory.Certificates.KronBallChebChain
public import LeanTheory.Certificates.KronBallChebDigits
public import LeanTheory.Certificates.KronBallChebEnv
public import LeanTheory.Certificates.KronBallChebFam
public import LeanTheory.Certificates.KronBallChebGrid
public import LeanTheory.Certificates.KronBallChebNorm
public import LeanTheory.Certificates.KronBallChebSpread
public import LeanTheory.Certificates.KronBallGrid
public import LeanTheory.Certificates.KronBallLowMem
public import LeanTheory.Certificates.KronChebCompute
public import LeanTheory.Certificates.KronExpr
public import LeanTheory.Certificates.KronLowMemCompute
public import LeanTheory.Certificates.KronProof
public import LeanTheory.Certificates.KronProof2D
public import LeanTheory.Certificates.Kronecker2D
public import LeanTheory.Certificates.Kronecker2DWeighted
public import LeanTheory.Certificates.PolyCert
public import LeanTheory.Certificates.PolyInterval
public import LeanTheory.Certificates.RouthHurwitz
public import LeanTheory.Certificates.RadiiPolynomial
public import LeanTheory.Certificates.RationalIntervals
public import LeanTheory.Certificates.SBP
public import LeanTheory.Certificates.SBPGeneral
public import LeanTheory.Certificates.ValidatedQuadrature
public import LeanTheory.Certificates.ValidatedQuadratureArcs
public import LeanTheory.Certificates.ValidatedTrig
public import LeanTheory.Certificates.ValidatedTrigFast
public import LeanTheory.Certificates.WeightedEll1
public import LeanTheory.Design.AntitheticMotif
public import LeanTheory.Design.AntitheticStability
public import LeanTheory.Design.EnvZOmpR
public import LeanTheory.Design.EnvZStability
public import LeanTheory.Elaborate
public import LeanTheory.Kernel.CME
public import LeanTheory.Kernel.Example
public import LeanTheory.Kernel.Homeostasis
public import LeanTheory.Kernel.MassAction
public import LeanTheory.Kernel.Network
public import LeanTheory.Kernel.Stability
public import LeanTheory.ResponseExt
public import LeanTheory.Sanity.CRNBlowUp
public import LeanTheory.Sanity.CRNCME
public import LeanTheory.Sanity.CRNClassStability
public import LeanTheory.Sanity.CRNExtinction
public import LeanTheory.Sanity.CRNHomeostasis
public import LeanTheory.Sanity.CRNMassAction
public import LeanTheory.Sanity.CRNNetwork
public import LeanTheory.Sanity.CRNStability
public import LeanTheory.Sanity.DeterminantFormula
public import LeanTheory.Sanity.Example
public import LeanTheory.Sanity.FosterLyapunov
public import LeanTheory.Sanity.PolyCert
public import LeanTheory.Sanity.QuasisymmetryNotSymmetry
public import LeanTheory.SubsetSum
public import LeanTheory.TaskHandlers
public import LeanTheory.Theory.CRN.AntitheticCME
public import LeanTheory.Theory.CRN.AntitheticFeedback
public import LeanTheory.Theory.CRN.ClassStability
public import LeanTheory.Theory.CRN.ConverseLyapunov
public import LeanTheory.Theory.CRN.ConverseLyapunovPD
public import LeanTheory.Theory.CRN.FiniteCME
public import LeanTheory.Theory.CRN.FosterLyapunov
public import LeanTheory.Theory.CRN.Linearization
public import LeanTheory.Theory.Fields.FieldLineExistence
public import LeanTheory.Theory.Homeostasis.DeterminantFormula
public import LeanTheory.Theory.Fields.InvariantBarrier
public import LeanTheory.Theory.Fields.LieGradient
public import LeanTheory.Theory.Fields.VectorCalculus
public import LeanTheory.Theory.KAM.AnalyticComposition
public import LeanTheory.Theory.KAM.AnalyticCompositionLip
public import LeanTheory.Theory.KAM.CauchyTwoVar
public import LeanTheory.Theory.KAM.Cohomological
public import LeanTheory.Theory.KAM.Composition
public import LeanTheory.Theory.KAM.Diophantine
public import LeanTheory.Theory.KAM.DiophantineB
public import LeanTheory.Theory.KAM.FourierSumHolo
public import LeanTheory.Theory.KAM.InvSqrt
public import LeanTheory.Theory.KAM.InvSqrtApprox
public import LeanTheory.Theory.KAM.KamSequence
public import LeanTheory.Theory.KAM.ParamInterp
public import LeanTheory.Theory.KAM.PolyExprS
public import LeanTheory.Theory.KAM.PolyExprSConstMono
public import LeanTheory.Theory.KAM.PolyExprSMajQ
public import LeanTheory.Theory.KAM.PolyExprSMajQG
public import LeanTheory.Theory.KAM.PolyExprSStrip
public import LeanTheory.Theory.KAM.SampledBound
public import LeanTheory.Theory.KAM.StripAlgebra
public import LeanTheory.Theory.KAM.StripEval
public import LeanTheory.Theory.KAM.StripPaleyWiener
public import LeanTheory.Theory.KAM.StripSmooth
public import LeanTheory.Theory.KAM.TorusFieldAna
public import LeanTheory.Theory.KAM.WeightedEll1Z2
public import LeanTheory.Theory.Markov.FiniteChain
public import LeanTheory.Theory.Stability.AbstractEnergy
public import LeanTheory.Theory.Stability.BlockBounds
public import LeanTheory.Theory.Stability.Newcomb
public import LeanTheory.Theory.Stability.RiccatiComparison
public import LeanTheory.Theory.Stability.Suydam

/-!
# LeanTheory: template library

Entry point of the template for formalizing a mathematical-physics theory with verified numerics:

* `Kernel/`: model laws stated as typeclasses (no axioms); `Kernel/Example` is a worked example;
* `Sanity/`: degenerate cases, concrete instances and counterexamples for each kernel law;
* `Bridge/`: composition theorems connecting kernel laws to theory results;
* `Theory/`: general mathematics (KAM/strip analysis, Sturm–Newcomb comparison, vector calculus,
  ODE barriers);
* `Certificates/`: certificate formats with soundness theorems and proof-term builders;
* `SubsetSum`: the reference pattern for building large proofs as explicit proof terms.
-/
