module

public import Theory.GroupTheory.SylowNormalIntersection
public import Theory.GroupTheory.SylowNormalizerFrattini
public import Theory.GroupTheory.LocalNormalizerUniqueness
public import Theory.GroupAction.TwoGroupFixedImage
public import Theory.GroupAction.SubgroupConjugation
public import Theory.PPrimeCore

/-!
# Odd centralizer cores under images of Sylow-central subgroups

Let B lie in the center of a Sylow two-subgroup S of a finite group G.
Every surjection f carries O(C_G(B)) into O(C_{f(G)}(f(B))), without
any restriction on its kernel. The same conclusion holds for an odd
normal subgroup of C_G(B) inside a normal domain for the action.

Set J = f⁻¹(f(B)) and P = S ∩ J. Since S normalizes J, P is Sylow in J.
Frattini gives f(N_G(P)) = N_{f(G)}(f(B)). Odd-kernel fixed-point lifting
identifies the image of O(C_G(B)) with the image of its centralizer of P.
The latter lies in O(C_G(P)), which is normalized by N_G(P). Its image
is therefore a normal odd subgroup of the full centralizer of f(B).

This is the Sylow-central specialization of the action argument in
Aschbacher, *Finite Group Theory*, second edition, 31.18(2), printed p.161.
Unlike an arbitrary inclusion of automizers, the normalizer surjection
justifies normality in the full target centralizer. The application is
Aschbacher–Smith, combined manuscript (1 March 2004), E.6.19, printed p.252.
-/

public section

open Subgroup
namespace Subgroup
variable {G H : Type*} [Group G] [Group H] [Finite G]

private theorem exists_sylow_intersection_of_normalizes
    (S : Sylow 2 G) (J : Subgroup G) (hSJ : (S : Subgroup G) ≤ normalizer (J : Set G)) :
    ∃ P : Sylow 2 J, (P : Subgroup J) = (S : Subgroup G).subgroupOf J := by
  let W := J ⊔ (S : Subgroup G)
  have hJW : J ≤ W := le_sup_left
  let _ : (J.subgroupOf W).Normal :=
    (normal_subgroupOf_iff_le_normalizer hJW).mpr (sup_le J.le_normalizer hSJ)
  obtain ⟨P, hP⟩ := (S.subtype (show (S : Subgroup G) ≤ W from le_sup_right)).exists_subgroupOf_eq_of_normal (J.subgroupOf W)
  let e := subgroupOfEquivOfLe hJW
  refine ⟨P.mapSurjective (f := e.toMonoidHom) e.surjective, ?_⟩
  change (P : Subgroup _).map e.toMonoidHom = _
  rw [hP]
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact hy
  · intro hx
    exact ⟨⟨⟨x, hJW x.property⟩, x.property⟩, hx, rfl⟩

private theorem normalizer_map_of_sylow_preimage
    (f : G →* H) (hf : Function.Surjective f) (B : Subgroup H)
    (P : Sylow 2 (B.comap f))
    (hPB : ((P : Subgroup (B.comap f)).map (B.comap f).subtype).map f = B) :
    (normalizer ((P : Subgroup (B.comap f)).map (B.comap f).subtype : Set G)).map f =
      normalizer (B : Set H) := by
  let J := B.comap f
  let R := (P : Subgroup J).map J.subtype
  apply le_antisymm
  · have hle := R.le_normalizer_map f
    rwa [hPB] at hle
  · let W := (normalizer (B : Set H)).comap f
    have hJW : J ≤ W := comap_mono B.le_normalizer
    have hWJ : W ≤ normalizer (J : Set G) :=
      (comap_normalizer_eq_of_surjective B hf).le
    have hfr := le_normalizer_sylow_sup J W hJW hWJ P
    have hm : W.map f ≤ (normalizer (R : Set G)).map f := by
      apply (map_mono hfr).trans
      rw [map_sup]
      apply sup_le le_rfl
      change (B.comap f).map f ≤ _
      rw [map_comap_eq_self_of_surjective hf, ← hPB]
      exact map_mono R.le_normalizer
    simpa only [W, map_comap_eq_self_of_surjective hf] using hm

private theorem map_odd_eq_map_centralizer_inf
    (f : G →* H) (R P : Subgroup G) (hodd : Odd (Nat.card R))
    (hP : IsPGroup 2 P) (hn : P ≤ normalizer (R : Set G))
    (hc : R.map f ≤ centralizer (P.map f : Set H)) :
    R.map f = (R ⊓ centralizer (P : Set G)).map f := by
  let _ : MulDistribMulAction P R := conjMulDistribMulActionOfLeNormalizer P R hn
  let actH : MulDistribMulAction P H :=
    { smul := fun _ x => x
      one_smul := fun _ => rfl
      mul_smul := fun _ _ _ => rfl
      smul_one := fun _ => rfl
      smul_mul := fun _ _ _ => rfl }
  let _ : MulDistribMulAction P H := actH
  let _ : MulAction P H := actH.toMulAction
  let r := f.comp R.subtype
  have hequiv : ∀ a : P, ∀ x : R, r (a • x) = a • r x := by
    intro a x
    change f ((a : G) * (x : G) * (a : G)⁻¹) = f x
    rw [map_mul, map_mul, map_inv, hc (mem_map_of_mem f x.property) _
      (mem_map_of_mem f a.property), mul_inv_cancel_right]
  have hf := r.map_fixedPoints_eq_of_odd_kernel hP
    (hodd.of_dvd_nat (card_subgroup_dvd_card r.ker)) hequiv
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    have hfx : r ⟨x, hx⟩ ∈ (FixedPoints.subgroup P R).map r := by
      rw [hf]
      exact ⟨⟨⟨x, hx⟩, rfl⟩, fun _ => rfl⟩
    obtain ⟨c, hc, he⟩ := hfx
    refine ⟨c, ⟨c.property, ?_⟩, he⟩
    intro a ha
    have hh := congrArg Subtype.val (hc (⟨a, ha⟩ : P))
    exact mul_inv_eq_iff_eq_mul.mp hh
  · exact map_mono inf_le_left

/-- For a subgroup in a Sylow two-center, its odd centralizer core maps into
that of the image under every surjection, with no condition on the kernel. -/
theorem map_oddCentralizer_le_of_sylow_central
    (f : G →* H) (hf : Function.Surjective f) (S : Sylow 2 G) (B : Subgroup G)
    (hBS : B ≤ (S : Subgroup G)) (hBC : B ≤ centralizer (S : Set G)) :
    (((pPrimeCore 2 (centralizer (B : Set G))).map (centralizer (B : Set G)).subtype).map f) ≤
      (pPrimeCore 2 (centralizer (B.map f : Set H))).map
        (centralizer (B.map f : Set H)).subtype := by
  let J := (B.map f).comap f
  have hSC : (S : Subgroup G) ≤ centralizer (B : Set G) := le_centralizer_iff.mp hBC
  have hSJ : (S : Subgroup G) ≤ normalizer (J : Set G) := by
    rw [← comap_normalizer_eq_of_surjective _ hf]
    exact map_le_iff_le_comap.mp ((map_mono hSC).trans
      ((map_centralizer_le_centralizer_image _ f).trans (centralizer_le_normalizer _)))
  obtain ⟨P₀, hP₀⟩ := exists_sylow_intersection_of_normalizes S J hSJ
  let P := (P₀ : Subgroup J).map J.subtype
  have hP : P = (S : Subgroup G) ⊓ J := by
    dsimp only [P]
    rw [hP₀, subgroupOf_map_subtype]
  have hBP : B ≤ P := by
    rw [hP]
    exact le_inf hBS (le_comap_map f B)
  have hPS : P ≤ (S : Subgroup G) := by rw [hP]; exact inf_le_left
  have hPf : P.map f = B.map f := by
    apply le_antisymm
    · exact map_le_iff_le_comap.mpr (by rw [hP]; exact inf_le_right)
    · exact map_mono hBP
  have hNP := normalizer_map_of_sylow_preimage f hf (B.map f) P₀ hPf
  let C := centralizer (B : Set G)
  let R := (pPrimeCore 2 C).map C.subtype
  have hRC : R ≤ C := map_subtype_le _
  have hRN : normalizer (B : Set G) ≤ normalizer (R : Set G) :=
    (le_normalizer_of_normal_subgroupOf (centralizer_le_normalizer (B : Set G))).trans
      (normalizer_le_normalizer_characteristic_image C (pPrimeCore 2 C))
  have hodd : Nat.Coprime 2 (Nat.card R) :=
    pPrimeCore_coprime_card.of_dvd_right (card_map_dvd _ _)
  have hfix : R.map f = (R ⊓ centralizer (P : Set G)).map f :=
    map_odd_eq_map_centralizer_inf f R P hodd.odd_of_left
      (S.isPGroup'.to_le hPS) (hPS.trans (hSC.trans ((centralizer_le_normalizer _).trans hRN)))
      (by rw [hPf]; exact (map_mono hRC).trans (map_centralizer_le_centralizer_image _ f))
  let CP := centralizer (P : Set G)
  let Z := (pPrimeCore 2 CP).map CP.subtype
  have hCPC : CP ≤ C := centralizer_le hBP
  have hRCP : R ⊓ CP ≤ Z := by
    have hn : (R.subgroupOf CP).Normal :=
      normal_subgroupOf_of_le_normalizer
        (hCPC.trans ((centralizer_le_normalizer _).trans hRN))
    have hcop : Nat.Coprime 2 (Nat.card (R.subgroupOf CP)) :=
      hodd.of_dvd_right (card_comap_dvd_of_injective R CP.subtype CP.subtype_injective)
    have hi : R.subgroupOf CP ≤ pPrimeCore 2 CP := le_sSup ⟨hn, hcop⟩
    simpa only [subgroupOf_map_subtype] using map_mono (f := CP.subtype) hi
  let D := centralizer (B.map f : Set H)
  have hZD : Z.map f ≤ D := by
    change Z.map f ≤ centralizer (B.map f : Set H)
    rw [← hPf]
    exact (map_mono (map_subtype_le (pPrimeCore 2 CP))).trans
      (map_centralizer_le_centralizer_image _ f)
  have hNZ : normalizer (P : Set G) ≤ normalizer (Z : Set G) :=
    (le_normalizer_of_normal_subgroupOf (centralizer_le_normalizer (P : Set G))).trans
      (normalizer_le_normalizer_characteristic_image CP (pPrimeCore 2 CP))
  have hDZ : D ≤ normalizer (Z.map f : Set H) := by
    apply (centralizer_le_normalizer (B.map f : Set H)).trans
    rw [← hNP]
    exact (map_mono hNZ).trans (Z.le_normalizer_map f)
  have hn : ((Z.map f).subgroupOf D).Normal :=
    (normal_subgroupOf_iff_le_normalizer hZD).mpr hDZ
  have hcop : Nat.Coprime 2 (Nat.card ((Z.map f).subgroupOf D)) :=
    pPrimeCore_coprime_card.of_dvd_right
      ((card_comap_dvd_of_injective (Z.map f) D.subtype D.subtype_injective).trans
        ((card_map_dvd Z f).trans (card_map_dvd (pPrimeCore 2 CP) CP.subtype)))
  have hi : (Z.map f).subgroupOf D ≤ pPrimeCore 2 D := le_sSup ⟨hn, hcop⟩
  have hi' : Z.map f ≤ (pPrimeCore 2 D).map D.subtype := by
    simpa only [map_subgroupOf_eq_of_le hZD] using map_mono (f := D.subtype) hi
  change R.map f ≤ _
  rw [hfix]
  exact (map_mono hRCP).trans hi'

end Subgroup

namespace Subgroup
variable {G H : Type*} [Group G] [Group H] [Finite G]

/-- The same image bound for an odd normal subgroup of a Sylow-central
centralizer, using a normal overgroup as the actual domain of the action. -/
theorem map_odd_subgroup_le_of_sylow_central_normal_domain
    (N : Subgroup G) [N.Normal] (f : N →* H) (hf : Function.Surjective f)
    (S : Sylow 2 G) (B R : Subgroup G)
    (hBS : B ≤ (S : Subgroup G)) (hBC : B ≤ centralizer (S : Set G))
    (hBN : B ≤ N) (hRN : R ≤ N) (hRC : R ≤ centralizer (B : Set G))
    (hn : centralizer (B : Set G) ≤ normalizer (R : Set G))
    (hodd : Nat.Coprime 2 (Nat.card R)) :
    (R.subgroupOf N).map f ≤
      (pPrimeCore 2 (centralizer ((B.subgroupOf N).map f : Set H))).map
        (centralizer ((B.subgroupOf N).map f : Set H)).subtype := by
  obtain ⟨S₀, hS₀⟩ := S.exists_subgroupOf_eq_of_normal N
  have hB₀ : B.subgroupOf N ≤ (S₀ : Subgroup N) := by
    rw [hS₀]
    exact comap_mono hBS
  have hc₀ : B.subgroupOf N ≤ centralizer (S₀ : Set N) := by
    intro b hb s hs
    change s ∈ (S₀ : Subgroup N) at hs
    rw [hS₀] at hs
    exact Subtype.ext (hBC hb s hs)
  have heC : centralizer (B.subgroupOf N : Set N) =
      (centralizer (B : Set G)).subgroupOf N := by
    ext x
    constructor
    · intro hc b hb
      exact congrArg Subtype.val (hc ⟨b, hBN hb⟩ hb)
    · intro hc b hb
      exact Subtype.ext (hc b hb)
  let C := centralizer (B.subgroupOf N : Set N)
  have hR₀ : R.subgroupOf N ≤ C := by
    dsimp only [C]
    rw [heC]
    exact comap_mono hRC
  have hn₀ : C ≤ normalizer (R.subgroupOf N : Set N) := by
    dsimp only [C]
    rw [← subgroupOf_normalizer_eq hRN, heC]
    exact comap_mono hn
  have hnormal : ((R.subgroupOf N).subgroupOf C).Normal :=
    (normal_subgroupOf_iff_le_normalizer hR₀).mpr hn₀
  have hcop : Nat.Coprime 2 (Nat.card ((R.subgroupOf N).subgroupOf C)) :=
    hodd.of_dvd_right
      ((card_comap_dvd_of_injective (R.subgroupOf N) C.subtype C.subtype_injective).trans
        (card_comap_dvd_of_injective R N.subtype N.subtype_injective))
  have hle : R.subgroupOf N ≤ (pPrimeCore 2 C).map C.subtype := by
    have hh : (R.subgroupOf N).subgroupOf C ≤ pPrimeCore 2 C :=
      le_sSup ⟨hnormal, hcop⟩
    simpa only [map_subgroupOf_eq_of_le hR₀] using map_mono (f := C.subtype) hh
  exact (map_mono hle).trans (map_oddCentralizer_le_of_sylow_central f hf S₀
    (B.subgroupOf N) hB₀ hc₀)

end Subgroup
