module

public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.SylowOvergroups.SmallModels
public import Theory.Alternating.Aut
public import Theory.SpecificGroups.Alternating.EvenPairCentralizer
public import Theory.SpecificGroups.AlternatingSix.ShadowLocal.InvolutionGeometry.Inner

/-!
# Alternating-group Sylow fixers in B.1.13

Outside degree six, automorphisms are induced by permutations. The even pair
flip subgroup has a two-group permutation centralizer, which bounds its
pointwise automorphism fixer. Sylow conjugacy then treats every Sylow subgroup.
For A₆, the centralizer in the full automorphism group of any inner involution
has order 32; this directly includes all exceptional automorphisms.

The faithful action on a perfect central quotient supplies the same bound
for central covers, in particular 3.A₆. The final theorem applies the bound
to the actual K-action on the source component and its local intersection.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), B.1.13,
printed p.74 (PDF p.85), and GLS3, Theorem 5.2.1 for the automorphism groups.
-/

public section
open Equiv Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterB.ComponentRecognition.SylowOvergroups

private theorem fixer_of_permutation_centralizer (m : ℕ) (hm : 5 ≤ m) (hm6 : m ≠ 6)
    (D : Subgroup (alternatingGroup (Fin m)))
    (hD : IsPGroup 2 (centralizer (D.map (alternatingGroup (Fin m)).subtype :
      Set (Perm (Fin m))))) :
    IsPGroup 2 (fixingSubgroup (MulAut (alternatingGroup (Fin m))) (D : Set (alternatingGroup (Fin m)))) := by
  let A := alternatingGroup (Fin m)
  let C := centralizer (D.map A.subtype : Set (Perm (Fin m)))
  let F := fixingSubgroup (MulAut A) (D : Set A)
  let f : C →* F := ((MulAut.conjNormal (H := A)).comp C.subtype).codRestrict _ (by
    intro c
    apply (mem_fixingSubgroup_iff _).mpr
    intro x hx
    apply Subtype.ext
    change c.val * x.val * c.val⁻¹ = x.val
    exact mul_inv_eq_iff_eq_mul.mpr
      (c.property x.val (mem_map_of_mem A.subtype hx)).symm)
  apply hD.of_surjective f
  intro a
  obtain ⟨g,hg⟩ :=
    (GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj m hm hm6).2 a.val
  have hc : g ∈ C := by
    rintro _ ⟨x,hx,rfl⟩
    have ha := (mem_fixingSubgroup_iff _).mp a.property x hx
    rw [← hg] at ha
    have he := congrArg Subtype.val ha
    change g * x.val * g⁻¹ = x.val at he
    exact (mul_inv_eq_iff_eq_mul.mp he).symm
  exact ⟨⟨g,hc⟩, Subtype.ext hg⟩

private theorem fixer_of_two_subgroup {G : Type*} [Group G] [Finite G]
    (D : Subgroup G) (hD : IsPGroup 2 D)
    (hfix : IsPGroup 2 (fixingSubgroup (MulAut G) (D : Set G))) :
    SylowFixerIsTwoGroup G := by
  intro S
  obtain ⟨Q,hDQ⟩ := hD.exists_le_sylow
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq G S Q
  let e := MulAut.conj g
  have he : (S : Subgroup G).map e.toMonoidHom = (Q : Subgroup G) := by
    have hh := congrArg (fun P : Sylow 2 G => (P : Subgroup G)) hg
    rw [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def] at hh
    exact hh
  let F := fixingSubgroup (MulAut G) (S : Set G)
  let E := fixingSubgroup (MulAut G) (D : Set G)
  let f : F →* E := ((MulAut.congr e).toMonoidHom.comp F.subtype).codRestrict _ (by
    intro a
    apply (mem_fixingSubgroup_iff _).mpr
    intro d hd
    have hdQ := hDQ hd
    rw [← he] at hdQ
    obtain ⟨x,hx,rfl⟩ := hdQ
    change e (a.val (e.symm (e x))) = e x
    have hx' := (mem_fixingSubgroup_iff _).mp a.property x hx
    change a.val x = x at hx'
    rw [e.symm_apply_apply, hx'])
  exact hfix.of_injective f (fun a b hab => Subtype.ext
    ((MulAut.congr e).injective (congrArg Subtype.val hab)))

/-- The full A₆ automorphism fixer is a two-group, including exceptional automorphisms. -/
theorem alternatingSix_fixer : SylowFixerIsTwoGroup (alternatingGroup (Fin 6)) := by
  intro S
  obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' (G := S) 2 (by
    rw [AlternatingSix.ShadowLocal.alternatingSylow_card]; decide)
  have hao : orderOf (a : alternatingGroup (Fin 6)) = 2 :=
    (orderOf_injective (S : Subgroup (alternatingGroup (Fin 6))).subtype
      (S : Subgroup (alternatingGroup (Fin 6))).subtype_injective a).trans ha
  apply (IsPGroup.of_card (p := 2) (n := 5)
    (AlternatingSix.ShadowLocal.inner_involution_centralizer_card a hao)).to_le
  intro β hβ
  rw [AlternatingSix.ShadowLocal.centralizer_inner_eq_stabilizer,
    MulAction.mem_stabilizer_iff]
  exact (mem_fixingSubgroup_iff _).mp hβ a a.property

/-- The pointwise fixer of any Sylow two-subgroup of Aₘ is a two-group. -/
theorem alternating_fixer (m : ℕ) (hm : 5 ≤ m) : SylowFixerIsTwoGroup (alternatingGroup (Fin m)) := by
  by_cases hm5 : m = 5
  · subst m; exact alternatingFive_fixer
  by_cases hm6 : m = 6
  · subst m; exact alternatingSix_fixer
  obtain ⟨D,hD,hC⟩ := Theory.SpecificGroups.Alternating.EvenPairCentralizer.exists_two_subgroup_centralizer m (by omega)
  exact fixer_of_two_subgroup D hD (fixer_of_permutation_centralizer m hm hm6 D hC)

/-- The alternating bound lifts to every perfect central cover, including 3.A₆. -/
theorem alternating_centralCover_fixer {L : Type*} [Group L] [Finite L]
    [Group.IsPerfect L] {m : ℕ} (hm : 5 ≤ m)
    (e : L ⧸ center L ≃* alternatingGroup (Fin m)) : SylowFixerIsTwoGroup L :=
  fixer_twoGroup_of_centralQuotient e (alternating_fixer m hm)

/-- The alternating models exclude the centralizing branch of the literal
local alternative in B.1.13, including the triple cover of A₆. -/
theorem alternating_le_component {G : Type*} [Group G] [Finite G]
    (K L : Subgroup G) (T : Sylow 2 G) {m : ℕ} (hm : 5 ≤ m)
    (hL : IsComponent G L) (hLK : ⁅L, K⁆ = L)
    (hkind : IsQuasisimple K ∨ Nat.card K = 3)
    (hKN : K ≤ normalizer (L : Set G))
    (e : L ⧸ center L ≃* alternatingGroup (Fin m))
    (hd : K ≤ L ∨ ⁅K, L ⊓ (K ⊔ (T : Subgroup G))⁆ = ⊥) : K ≤ L := by
  let := hL.2
  exact le_component_of_local_dichotomy K L T hL hLK hkind hKN hd
    (alternating_centralCover_fixer hm e)

end CFSG.Quasithin.ChapterB.ComponentRecognition.SylowOvergroups
