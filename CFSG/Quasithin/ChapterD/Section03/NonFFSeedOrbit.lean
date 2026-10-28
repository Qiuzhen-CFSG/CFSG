module
public import CFSG.Quasithin.ChapterD.Section03.SeedCubic

/-!
# Collapsing an independent orbit of a non-FF seed

Faithfulness of the normal generalized Fitting subgroup on the seed persists
on each conjugate. Its elementary pointwise kernels vanish because the
ambient two-core is trivial. A minimum cubic actor would therefore make the
seed an FF-module if its independent orbit had more than one member.

The original central Hall tensor applies this to its actual local orbit
image in `SeedAnalysis/NaturalTensorLocal`, preserving the pointwise kernels.
Source: Aschbacher--Smith D.2.9 and D.3.5--6, printed pp.180--182,195--197,
refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Representation.BinaryOffender.Homogeneous
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterD
open Chapter3.Section02.ChosenSource325
variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V] (ρ : Representation (ZMod 2) G V)

/-- A non-FF constituent faithful on the normal generalized Fitting subgroup
has trivial orbit when the whole action has cubic ratio at most two. -/
theorem seed_invariant_of_nonFF_independent_orbit
    (K : Subgroup G) [K.Normal] (hF : generalizedFitting G = K)
    (hcore : pCore 2 G = ⊥)
    (I : Submodule (ZMod 2) V) (hKI : K ≤ subspaceStabilizer ρ I)
    (hk : subspaceKernel ρ I K = ⊥)
    (hind : sSupIndep (subspaceOrbit ρ ⊤ I))
    (hdim : 2 < Module.finrank (ZMod 2) I)
    (hb : cubicRatio ρ ≤ 2)
    (hnff : ¬ IsFFModule (subspaceImageRepresentation ρ I)) :
    (⊤ : Subgroup G) ≤ subspaceStabilizer ρ I := by
  obtain ⟨A,hA⟩ := (QhatStar_nonempty_iff ρ).mpr hb
  let : IsElementaryAbelian 2 A := hA.1.2.1.2
  have hker (t : G) : subspaceKernel ρ (I.map (ρ t)) A = ⊥ := by
    apply subspaceKernel_eq_bot_of_faithful_fitting ρ K hF hcore
    · intro k hk
      apply (subspace_map_eq_iff ρ (I.map (ρ t)) k).mp
      have hkt : t⁻¹*k*t ∈ K := by simpa only [inv_inv] using (inferInstance : K.Normal).conj_mem k hk t⁻¹
      have hfix := (subspace_map_eq_iff ρ I (t⁻¹*k*t)).mpr (hKI hkt)
      calc
        (I.map (ρ t)).map (ρ k) = I.map (ρ (k*t)) := (subspace_map_mul ρ I k t).symm
        _ = I.map (ρ (t*(t⁻¹*k*t))) := by congr 2; group
        _ = (I.map (ρ (t⁻¹*k*t))).map (ρ t) := subspace_map_mul ρ I t _
        _ = I.map (ρ t) := by rw [hfix]
    · apply bot_unique
      rintro k ⟨hkK,hfix⟩
      have hkt : t⁻¹*k*t ∈ subspaceKernel ρ I K := by
        refine ⟨by simpa only [inv_inv] using (inferInstance : K.Normal).conj_mem k hkK t⁻¹,?_⟩
        intro v hv
        have he := hfix (ρ t v) (Submodule.mem_map_of_mem hv)
        change ρ k (ρ t v) = ρ t v at he
        calc
          ρ (t⁻¹*k*t) v = ρ t⁻¹ (ρ k (ρ t v)) := by simp only [map_mul,Module.End.mul_apply]
          _ = v := by rw [he,←Module.End.mul_apply,←map_mul,inv_mul_cancel,map_one,Module.End.one_apply]
      have he := mem_bot.mp (hk.le hkt)
      exact mem_bot.mpr (calc
        k = t*(t⁻¹*k*t)*t⁻¹ := by group
        _ = 1 := by rw [he]; group)
    · exact IsElementaryAbelian.isPGroup 2 A
  intro t _
  apply (subspace_map_eq_iff ρ I t).mp
  by_contra hm
  exact hnff (isFFModule_of_cubic_actor_on_independent_orbit ρ I A hA.1.2.1
    hA.1.2.2.1 hind hdim
    ((actionRatio_le_nat_iff ρ hA.1.2.1 2).mp (hA.1.2.2.2.le.trans hb))
    hker ⟨t,hm⟩)

end CFSG.Quasithin.ChapterD
