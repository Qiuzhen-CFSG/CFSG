module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalLinearFieldParity.DisplacementConstituents
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalLinearFieldParity.DisplacementDegree
public import CFSG.Quasithin.ChapterH.Section01To04.L3Four.SchurField
public import Theory.Representation.SevenMultiplicity
/-!
# The order-seven displacement calculation on a homogeneous section

In degree three the left Cartan has order seven. Natural-seed generation
makes every nonidentity Cartan element fixed-free on the literal U/Z₁,
so it acts nontrivially on every nonzero invariant submodule. H.4.7 bounds
the Schur field of a faithful residual constituent by four. The commuting
order-seven action therefore forces three independent copies, each with
involution displacement at least three. Monotonicity transfers their nine
dimensions to the original relative-index displacement.

The submodule and its homogeneous residual constituent remain explicit
inputs. Selecting this section in the source configuration, establishing
5.1.16(2), and completing the global TI/F.8 geometry all remain with
qt-d-1222-linear-field-parity. This calculation alone is not a proof of
5.1.17 or unconditional parity.

Source: Aschbacher–Smith 5.1.17, printed p.641, using H.4.7, pp.382–383
(refs/quasithin.pdf).
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped MonoidAlgebra
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.LinearParity
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L H A B : Subgroup G}
  {X : Type*} [AddCommGroup X] [Module (ZMod 2) X] [FiniteDimensional (ZMod 2) X]

set_option backward.isDefEq.respectTransparency false in
/-- A homogeneous faithful section contributes nine dimensions in degree three. -/
theorem degree_three_homogeneous_section_displacement (s : Seed T L H A 3)
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ 3))
    (hTH : (T : Subgroup G) ≤ H)
    (hm : ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    (c : CartanPair T L H A B)
    (e : ((H ⧸ pCore 2 H) × A) ≃*
      ((H ⊔ A : Subgroup G) ⧸ pCore 2 (H ⊔ A : Subgroup G)))
    (he : ∀ (x : H) (a : A),
      e (QuotientGroup.mk' (pCore 2 H) x, a) =
        QuotientGroup.mk' (pCore 2 (H ⊔ A : Subgroup G))
          ⟨(x : G) * (a : G), mul_mem_sup x.property a.property⟩)
    (ρ : Representation (ZMod 2)
      ((H ⊔ A : Subgroup G) ⧸ pCore 2 (H ⊔ A : Subgroup G)) X)
    (d : BinaryConjugationSection (H ⊔ A) (setup T L s.V H A).U
      (setup T L s.V H A).V₁
      (ρ.comp (QuotientGroup.mk' (pCore 2 (H ⊔ A : Subgroup G)))))
    (P : Subrepresentation ρ)
    (I : Subrepresentation (residualFactorAction e P.toRepresentation))
    (hi : IsIrreducible I.toRepresentation)
    (hh : Homogeneous.homogeneousPart I ⊤ = ⊤)
    (hf : Function.Injective I.toRepresentation)
    (hir : IsIrreducible (I.toRepresentation.comp
      (generalizedFitting (H ⧸ pCore 2 H)).subtype))
    {y : G} (hy : y ∈ H) (hy2 : y ^ 2 ∈ H.pCoreIn 2) (hyQ : y ∉ H.pCoreIn 2) :
    9 ≤ displacement (setup T L s.V H A) y := by
  revert I
  rw [residualFactorAction_eq]
  intro I hi hh hf hir
  let σ := P.toRepresentation.comp (e.toMonoidHom.comp (MonoidHom.inl _ _))
  let τ : Representation (ZMod 2) A P.toSubmodule :=
    P.toRepresentation.comp (e.toMonoidHom.comp (MonoidHom.inr _ _))
  have hcomm (a : A) (m : H ⧸ pCore 2 H) (v : P.toSubmodule) : τ a (σ m v) = σ m (τ a v) := by
    have hp : Commute ((1,a) : (H ⧸ pCore 2 H) × A) (m,1) := by
      exact show (1,a) * (m,1) = (m,1) * (1,a) by simp
    exact LinearMap.congr_fun ((hp.map e).map P.toRepresentation).eq v
  have hcard : Nat.card A = 7 := by
    simpa using (c.left_cyclic_and_card hTL hpsl).2
  let : Nontrivial A := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨a,ha⟩ := exists_ne (1 : A)
  have ha7 : a ^ 7 = 1 := by
    rw [← hcard]
    exact pow_card_eq_one'
  have hτ : τ a ≠ 1 := by
    intro hz
    let := hi
    let : Nontrivial I.toSubmodule := Subrepresentation.irreducible_module_nontrivial I.toRepresentation
    obtain ⟨v,hv⟩ := exists_ne (0 : I.toSubmodule)
    apply hv
    apply Subtype.ext
    apply Subtype.ext
    apply s.cartan_fixedFree c ρ d a ha
    have he' := he 1 a
    have he'' : e (1,a) = QuotientGroup.mk' (pCore 2 (H ⊔ A : Subgroup G))
        ⟨a,mem_sup_right a.property⟩ := by simpa using he'
    have hv' := congrArg (fun z : P.toSubmodule => (z : X))
      (LinearMap.congr_fun hz (v : P.toSubmodule))
    change ρ (e (1,a)) ((v : P.toSubmodule) : X) = ((v : P.toSubmodule) : X) at hv'
    rw [← he'']
    exact hv'
  obtain ⟨F,_,_,hF,⟨f⟩⟩ := residual_coreQuotient_fitting_model hTH hm
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow (f := 2)
    (by simpa only [Nat.card_eq_fintype_card, show (2:ℕ)^2=4 from rfl] using hF)
  let := hi
  let := hir
  have hSchur := ChapterH.Section01To04.L3Four.source_schurField_card hF f.symm I.toRepresentation hf
  have hb := SevenMultiplicity.triple_fixedCodim_le_of_order_seven σ I hi hh hSchur τ hcomm a ha7 hτ
    (QuotientGroup.mk' (pCore 2 H) ⟨y,hy⟩)
  have hI := residual_constituent_displacement hTH hm σ I hf hir hy hy2 hyQ
  let P' : Subrepresentation (residualFactorAction e ρ) :=
    ⟨P.toSubmodule,fun g v hv => by
      rw [residualFactorAction_eq]
      exact P.apply_mem_toSubmodule (e (g,1)) hv⟩
  have hmono := fixedCodim_subrepresentation_le (residualFactorAction e ρ) P'
    (zpowers (QuotientGroup.mk' (pCore 2 H) ⟨y,hy⟩))
  have hP' : P'.toRepresentation = σ := by
    apply MonoidHom.ext
    intro g
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    change (residualFactorAction e ρ) g (v : X) = ρ (e (g,1)) (v : X)
    exact congrArg (fun μ : Representation (ZMod 2) (H ⧸ pCore 2 H) X =>
      μ g (v : X)) (residualFactorAction_eq e ρ)
  rw [hP'] at hmono
  rw [displacement_eq_residualFactor_fixedCodim s.f8 e he ρ d hy]
  omega
end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.LinearParity
