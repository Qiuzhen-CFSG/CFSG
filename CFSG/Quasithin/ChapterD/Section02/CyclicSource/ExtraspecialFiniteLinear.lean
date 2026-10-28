module
public import CFSG.Quasithin.ChapterD.Section02.CyclicSource.ExtraspecialNormalizerEndpoint
public import Theory.Representation.ExtraspecialBinarySix

/-!
# The finite-linear completion of the extraspecial source branch

On the actual binary six-space, centrality of the cubic center puts the
involution-generated actor in SL₃(4). Its three-part is only27, so the local
extraspecial commutator equals the whole three-core. Its faithful centralizer
is contained in it; the center-fixing Frattini action then supplies the
original selected involution as a cyclic supplement.
Source: Aschbacher–Smith D.2.29, printed p.192.
-/

@[expose] public section
open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterD.CyclicSource
variable {G V : Type*} [Group G] [Finite G]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V}

/-- The exact three-core and generation identities required by the local
endpoint classifier, without a linear normalizer premise. -/
theorem CoreHypotheses.extraspecial_threeCore_generation (h : CoreHypotheses ρ)
    (t : G) (ht : t ∈ smallSupportInvolutions ρ)
    (hF : IsExtraspecial 3 (⁅pCore 3 G,zpowers t⁆ : Subgroup G))
    (hc : Nat.card (⁅pCore 3 G,zpowers t⁆ : Subgroup G) = 27)
    (hd : Module.finrank (ZMod 2) V = 6)
    (hZ : (center (⁅pCore 3 G,zpowers t⁆ : Subgroup G)).map
      (⁅pCore 3 G,zpowers t⁆ : Subgroup G).subtype ≤ center G) :
    pCore 3 G = ⁅pCore 3 G,zpowers t⁆ ∧
      (⁅pCore 3 G,zpowers t⁆ : Subgroup G) ⊔ zpowers t = ⊤ := by
  let F := (⁅pCore 3 G,zpowers t⁆ : Subgroup G)
  let : IsExtraspecial 3 F := hF
  have hFP : F ≤ pCore 3 G := commutator_le_left (pCore 3 G) (zpowers t)
  have hdiv : Nat.card G ∣ 60480 := ExtraspecialBinarySix.card_dvd_specialLinear
    ρ F h.faithful hc hd hZ h.involution_generated
  obtain ⟨n,hn⟩ := (pCore_isPGroup (p := 3) (G := G)).exists_card_eq
  have hpow : 3 ^ n ∣ 60480 := by
    rw [← hn]
    exact (card_subgroup_dvd_card (pCore 3 G)).trans hdiv
  have hnle : n ≤ 3 := by
    by_contra hbad
    have hle : 4 ≤ n := by omega
    have hh : 3 ^ 4 ∣ 60480 := (Nat.pow_dvd_pow 3 hle).trans hpow
    norm_num at hh
  have hcard : Nat.card (pCore 3 G) ≤ 27 := by
    rw [hn]
    exact Nat.pow_le_pow_right (by decide : 0 < 3) hnle
  have hcF : Nat.card F = 27 := hc
  have he : F = pCore 3 G := eq_of_le_of_card_ge hFP (by simpa only [hcF] using hcard)
  let : F.Normal := he.symm ▸ inferInstance
  have hC : centralizer (F : Set G) ≤ F :=
    ExtraspecialBinarySix.centralizer_le ρ F h.faithful hc hd
  exact ⟨he.symm,h.extraspecial_normalizer_endpoint F hc hC hZ t ht⟩

end CFSG.Quasithin.ChapterD.CyclicSource
