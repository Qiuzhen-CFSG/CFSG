module
public import Theory.SpecificGroups.PSL3Four.CentralCover.FullPlaneNormalizer
public import Theory.GroupTheory.PerfectOddIndexNormalizer
public import Theory.GroupTheory.EmbeddedCenterMap
/-!
# Equal centers of the original opposite lifted parabolics

The normalizer of the conjugate elementary core is a perfect full parabolic.
It normalizes the conjugate block and contains its Sylow subgroup. The odd
quotient therefore vanishes, and equal orders identify those same subgroups.
Their embedded centers are the original central kernel. No assumption that
the conjugating element normalizes the overcomponent is used.
Source: Aschbacher–Smith 2.4.11, printed p.532.
-/
public section
open Subgroup
namespace Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G]
lemma psl_three_four_opposite_center
    (K L Q R : Subgroup G) [Group.IsPerfect K] (a : MulAut G)
    (f : K →* Matrix.PSL3Four.PSL) (hf : Function.Surjective f)
    (hfker : f.ker = center K)
    (hLK : L ≤ K) (hRQ : Q ≤ R) (hRL : R ≤ L)
    (hQelem : IsElementaryAbelian 2 Q) (hQc : Nat.card Q = 64)
    (hLc : Nat.card L = 3840) (hRc : Nat.card R = 256)
    (haR : R.map a.toMonoidHom = R)
    (hLQ : L ≤ normalizer (Q : Set G))
    (hN : normalizer (Q : Set G) = normalizer (L : Set G))
    (hZ : (center K).map K.subtype = (center L).map L.subtype)
    (hZc : Nat.card (center K) = 4)
    (hZQa : (center K).map K.subtype ≤ Q.map a.toMonoidHom) :
    ((center L).map L.subtype).map a.toMonoidHom = (center L).map L.subtype := by
  let A := Q.map a.toMonoidHom
  let L' := L.map a.toMonoidHom
  have hAR : A ≤ R := (map_mono hRQ).trans_eq haR
  have hAK : A ≤ K := hAR.trans (hRL.trans hLK)
  let V := A.subgroupOf K
  let := hQelem
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.map a.toMonoidHom
  let : IsElementaryAbelian 2 V := IsElementaryAbelian.subgroupOf hAK
  have hkV : f.ker ≤ V := by
    rw [hfker]
    intro k hk
    exact hZQa (mem_map_of_mem K.subtype hk)
  have hVc : Nat.card V = Nat.card f.ker * 16 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hAK).toEquiv,
      card_map_of_injective a.injective,hQc,hfker,hZc]
  obtain ⟨hp,hcard,hcenter⟩ := Matrix.PSL3Four.FullPlaneNormalizer.full_plane_normalizer
    f hf (by rw [hfker]) V hkV hVc
  let P := normalizer (V : Set K)
  let N := P.map K.subtype
  have hPc : Nat.card P = 3840 := by simpa only [hfker,hZc] using hcard
  have hNc : Nat.card N = 3840 := (card_map_of_injective K.subtype_injective).trans hPc
  let : Group.IsPerfect P := hp
  let : Group.IsPerfect N := Group.IsPerfect.map K.subtype
  have hAN : N ≤ normalizer (A : Set G) := by
    have hh := V.le_normalizer_map K.subtype
    rwa [map_subgroupOf_eq_of_le hAK] at hh
  have hN' : N ≤ normalizer (L' : Set G) := by
    have he : normalizer (A : Set G) = normalizer (L' : Set G) := by
      change normalizer (Q.map a.toMonoidHom : Set G) = normalizer (L.map a.toMonoidHom : Set G)
      rw [←map_equiv_normalizer_eq,←map_equiv_normalizer_eq,hN]
    exact hAN.trans_eq he
  have hRLa : R ≤ L' := (map_mono hRL).trans' (by rw [haR])
  have hRA : R ≤ normalizer (A : Set G) := by
    have hh := (map_mono (hRL.trans hLQ)).trans (Q.le_normalizer_map a.toMonoidHom)
    rwa [haR] at hh
  have hRN : R ≤ N := by
    intro r hr
    refine ⟨⟨r,(hRL.trans hLK) hr⟩,?_,rfl⟩
    change (⟨r,(hRL.trans hLK) hr⟩ : K) ∈ normalizer (A.subgroupOf K : Set K)
    rw [←subgroupOf_normalizer_eq hAK]
    exact hRA hr
  have hRi : (R.subgroupOf N).index = 15 := by
    have hc : Nat.card (R.subgroupOf N) = 256 :=
      (Nat.card_congr (subgroupOfEquivOfLe hRN).toEquiv).trans hRc
    have he := (R.subgroupOf N).card_mul_index
    rw [hc,hNc] at he
    omega
  have hNL' : N ≤ L' := perfect_le_of_normalizes_of_odd_relIndex N L' R hN' hRLa (by rw [hRi]; decide)
  have hNL : N = L' := eq_of_le_of_card_ge hNL' (by
    rw [card_map_of_injective a.injective,hLc,hNc])
  have hcN : (center N).map N.subtype = (center K).map K.subtype := by
    have he := congrArg (fun X : Subgroup K => X.map K.subtype) hcenter
    rw [P.map_embeddedCenter K.subtype K.subtype_injective,hfker] at he
    exact he
  calc
    ((center L).map L.subtype).map a.toMonoidHom = (center L').map L'.subtype :=
      L.map_embeddedCenter a.toMonoidHom a.injective
    _ = (center N).map N.subtype := congrArg (fun X : Subgroup G => (center X).map X.subtype) hNL.symm
    _ = (center L).map L.subtype := hcN.trans hZ
end Theory.GroupTheory
