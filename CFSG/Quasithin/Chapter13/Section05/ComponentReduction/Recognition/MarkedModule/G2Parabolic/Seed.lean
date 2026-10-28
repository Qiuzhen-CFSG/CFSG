module

public import CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Recognition.MarkedModule.Basic
public import Theory.Representation.BinaryOffender.IrreducibleCentralSeed
public import Theory.Representation.BinaryOffender.ConjugationImage

/-!
# The original seed avoids the central kernel

Pull the intersection of the marked seed with the component-fixed space
back through U_H → U_H/V₁. The literal F.9 irreducibility hypothesis says
that its ambient subgroup is V₁ or V₃. The latter would make all seed
L₁-commutators zero, contradicting the two-dimensional seed. Hence the
seed injects into the actual central quotient, without any assumption
about irreducibility or splitting of the whole module.

Source: Aschbacher–Smith, F.9.1 and 13.5.21(iii),(5), printed p.924 /
PDF p.941. All subgroup and quotient maps are the original source maps.
-/

@[expose] public section
open scoped IsMulCommutative
open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Recognition.MarkedModule.G2Parabolic
open Section08.Source
variable {G : Type*} [Group G] [Finite G]
  (D : ChapterF.Section09.Setup G) (h : D.Hypothesis)
  [(D.V₁.subgroupOf D.UH).Normal] [IsElementaryAbelian 2 (Action.ModuleGroup D)]

/-- The original F.9 irreducibility forces the marked seed to avoid the
component-fixed subspace. No irreducibility of the whole module is assumed. -/
theorem seed_disjoint (K : Subgroup G) [(starImage D.H K).Normal]
    (hLK : D.L₁ ≤ K)
    (hdim : Module.finrank (ZMod 2) (Action.seedSpace D) = 2)
    (hgen : Action.seedSpace D = subspaceCommutator (Action.starRepresentation D h)
      (Action.seedSpace D) (starImage D.H D.L₁)) :
    Disjoint (Action.seedSpace D) (fixedSpace (Action.starRepresentation D h) (starImage D.H K)) := by
  let ρ := Action.starRepresentation D h
  let C := Action.seedSpace D ⊓ fixedSpace ρ (starImage D.H K)
  let π := QuotientGroup.mk' (D.V₁.subgroupOf D.UH)
  let J := (binarySubgroup C).comap π ⊓ D.Vplus.subgroupOf D.UH
  let E := J.map D.UH.subtype
  have hpoint : D.V₁ ≤ E := by
    intro v hv
    let u : D.UH := ⟨v, le_conjugateSpanBy D.Vplus D.H (h.point_lt.le hv)⟩
    refine ⟨u, ⟨?_,h.point_lt.le hv⟩,rfl⟩
    change π u ∈ binarySubgroup C
    have hu : π u = 1 := (QuotientGroup.eq_one_iff u).mpr hv
    rw [hu]
    exact one_mem _
  have hEV : E ≤ D.Vplus := by
    rintro _ ⟨u,hu,rfl⟩
    exact hu.2
  have hn : D.L₁ ⊔ (D.T : Subgroup G) ≤ normalizer (E : Set G) := by
    apply le_normalizer_iff.mpr
    rintro x hx _ ⟨u,hu,rfl⟩
    let xH : D.H := ⟨x,h.local_le hx⟩
    let u' : D.UH := ⟨x*u.val*x⁻¹, le_normalizer_iff.mp
      (le_normalizer_conjugateSpanBy D.Vplus D.H) x xH.property u.val u.property⟩
    have hv : u'.val ∈ D.Vplus := le_normalizer_iff.mp h.local_normalizes x hx u.val hu.2
    refine ⟨u',⟨?_,hv⟩,rfl⟩
    change Additive.ofMul (π u') ∈ C
    refine ⟨?_,?_⟩
    · exact ⟨u',hv,rfl⟩
    · rw [← Action.starRepresentation_apply D h xH u]
      exact (fixedSpace_stable_of_normalizes ρ (show (⊤ : Subgroup (Hstar D.H)) ≤
        normalizer (starImage D.H K : Set (Hstar D.H)) from le_normalizer_of_normal)
        (mem_top _) _).mpr hu.1.2
  rcases h.irreducible E hpoint hEV hn with hE | hE
  · apply Submodule.disjoint_def.mpr
    intro v hv hf
    obtain ⟨u,hu,rfl⟩ := hv
    have huE : u.val ∈ E := ⟨u,⟨⟨⟨u,hu,rfl⟩,hf⟩,hu⟩,rfl⟩
    rw [hE] at huE
    have hu1 : π u = 1 := (QuotientGroup.eq_one_iff u).mpr huE
    exact congrArg Additive.ofMul hu1
  · have hf : Action.seedSpace D ≤ fixedSpace ρ (starImage D.H D.L₁) := by
      rintro v ⟨u,hu,rfl⟩ l
      have huE : u.val ∈ E := by rw [hE]; exact hu
      obtain ⟨w,hw,he⟩ := huE
      have hwu : w = u := Subtype.ext he
      subst w
      exact hw.1.2 ⟨l.val, (map_mono (comap_mono hLK)) l.property⟩
    have hz : Action.seedSpace D = ⊥ := hgen.trans ((subspaceCommutator_eq_bot_iff ρ _ _).mpr hf)
    rw [hz,finrank_bot] at hdim
    omega
end CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Recognition.MarkedModule.G2Parabolic
