module
public import CFSG.Quasithin.Chapter8.Section02.HermitianSourceActorRankGap
public import CFSG.Quasithin.Chapter8.Section02.HermitianSourceGeometricTorus
import all CFSG.Quasithin.Chapter8.Section02.HermitianSourceSelectedTorusBounds
import all CFSG.Quasithin.Chapter8.Section02.HermitianSourceActorRankGap

/-!
# The remaining selected Hermitian endpoint

The strict actor-rank gap makes the actor larger than 2n at k = 2n.
Its fixed space has rank at most 4n. Together with the original rank
identity and fixed-field divisibility for the odd torus, this leaves only
actor ranks 3n and 4n. In the maximal case the actor is the plane radical;
the induced odd similitude would fix three dimensions of its minus form,
which is impossible. Thus the remaining actor has rank 3n and the literal
torus fixed space has rank 4n.

No E.2.14 rank clause is used. This does not exclude the remaining endpoint:
its linear-module or scalar-torus argument is still needed. Selection,
E.2.14's torus identity and the field-four normalizer/centralizer endgame
remain with the original Hermitian exclusion. Half-degree one is retained.
The Chapter 12 EndpointRanks extension applies this to the chosen tensor.

Source: Aschbacher–Smith E.2.14(7,9), printed pp.226–228, H.4.4,
printed p.381, and 8.2.3, printed pp.715–716 (refs/quasithin.pdf).
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter8.Section02.HermitianSource
open ChapterE Offenders.Parabolic Offenders.Parabolic.Construction
variable {G : Type*} [Group G] [Finite G]
  {H T M V I : Subgroup G} [IsElementaryAbelian 2 V]
  {k : ℕ} {i : I} {S : Sylow 2 I}

open Representation Representation.HermitianTensorThree
open Representation.HermitianTensorThree.ImageOuter
open Representation.HermitianTensorThree.ParabolicTorus

private theorem endpoint_arithmetic (n a b f c : ℕ)
    (hn : 0 < n) (hu : a ≤ 4*n) (hc : 5*n ≤ c)
    (hs : c+b = 9*n) (hf : f ≤ b) (hi : f+2*n+a = 9*n)
    (hd : n ∣ f) : (a = 3*n ∧ f = 4*n) ∨ (a = 4*n ∧ f = 3*n) := by
  obtain ⟨d,hd⟩ := hd
  have hlo : 3 ≤ d := by nlinarith
  have hhi : d ≤ 4 := by nlinarith
  rcases (show d = 3 ∨ d = 4 by omega) with rfl | rfl
  · exact Or.inr ⟨by omega,by omega⟩
  · exact Or.inl ⟨by omega,by omega⟩

private theorem endpoint_fixed_large (n a f : ℕ) (hu : a ≤ 4*n)
    (hi : f+2*n+a = 9*n) (hne : a ≠ 4*n) : 3*n < f := by omega

private theorem endpoint_fixed_eq (n a f : ℕ) (hi : f+2*n+a = 9*n)
    (ha : a = 4*n) : f = 3*n := by omega

/-- Before using the E.2.14 rank clause, the endpoint has only two
possible actor ranks. The nonmaximal case has torus fixed rank 4n. -/
theorem selected_endpoint_actor_rank_alternative
    (s : Selected H T M V I k i S) (n : ℕ) [NeZero n] (hkn : k = 2*n)
    (e : Additive V ≃ₗ[ZMod 2] Space n)
    (j : Automizer V →* binaryNormalizer n) (hj : Function.Injective j)
    (he : ∀ a v, e (automizerRepresentation V a v) =
      overgroupAction n (binaryNormalizer n) (j a) (e v))
    (x : Automizer V) (ho : orderOf x = 2^k-1)
    (hfixed : automizerFixedGroup V (zpowers x) =
      V ⊓ V.map (MulAut.conj i.val⁻¹).toMonoidHom) :
    let A := V.map (MulAut.conj i.val⁻¹).toMonoidHom ⊓ (pCore 2 I).map I.subtype
    (rank (inducedAutomizer V A) = 3*n ∧
      Module.finrank (ZMod 2) (fixedSpace (automizerRepresentation V) (zpowers x)) = 4*n) ∨
    (rank (inducedAutomizer V A) = 4*n ∧
      Module.finrank (ZMod 2) (fixedSpace (automizerRepresentation V) (zpowers x)) = 3*n) := by
  let W := V.map (MulAut.conj i.val⁻¹).toMonoidHom
  let A := W ⊓ (pCore 2 I).map I.subtype
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.map _
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.of_le (show A ≤ W from inf_le_left)
  let : IsElementaryAbelian 2 (inducedAutomizer V A) :=
    inducedAutomizer_elementary V A (actor_normalizes s)
  let : IsElementaryAbelian 2 ((inducedAutomizer V A).map j) := IsElementaryAbelian.map j
  have ha : 2*n < rank (inducedAutomizer V A) := by
    simpa only [hkn] using selected_actor_rank_gt_parameter s
  have hupper : rank (inducedAutomizer V A) ≤ 4*n :=
    (offender_rank_le_primeRank _).trans ((primeRank_le_of_injective 2 j hj).trans
      (OuterRank.normalizer_twoRank_le n (normalizerCoverage n) ⟨FieldSections.centralizerEquiv n⟩))
  have hBr : 2*n < rank ((inducedAutomizer V A).map j) := by
    rwa [rank_map_injective j hj]
  have hc := overgroup_fixedCodim_of_rank_gt_two_mul n (binaryNormalizer n) le_rfl
    ((inducedAutomizer V A).map j) hBr
  rw [←fixedCodim_map_equivariant (automizerRepresentation V)
    (overgroupAction n (binaryNormalizer n)) j e he] at hc
  have hdim : Module.finrank (ZMod 2) (Additive V) = 9*n := e.finrank_eq.trans (finrank_binary n)
  have hvr : rank V = 9*n := by
    rw [rank,show Nat.card V = Nat.card (Additive V) from rfl,
      Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod,hdim,
      Nat.log_pow Nat.one_lt_two]
  have hz := fixedGroup_rank (V := V) (zpowers x)
  rw [hfixed] at hz
  have hid := selected_actor_rank_identity s
  change rank (V ⊓ W) + k + rank (inducedAutomizer V A) = rank V at hid
  change rank (V ⊓ W) = _ at hz
  rw [hz,hkn,hvr] at hid
  have hfixle := Submodule.finrank_mono (selected_fixedSpace_le_actor s x hfixed)
  have hsum := fixedCodim_add_finrank (automizerRepresentation V) (inducedAutomizer V A)
  rw [hdim] at hsum
  dsimp only
  change (_ = _ ∧ _ = _) ∨ (_ = _ ∧ _ = _)
  by_cases hmax : rank (inducedAutomizer V A) = 4*n
  · exact Or.inr ⟨hmax,endpoint_fixed_eq n _ _ hid hmax⟩
  have hlarge : 3*n < Module.finrank (ZMod 2)
      (fixedSpace (automizerRepresentation V) (zpowers x)) :=
    endpoint_fixed_large n _ _ hupper hid hmax
  have hm : Module.finrank (ZMod 2) (fixedSpace (automizerRepresentation V) (zpowers x)) =
      Module.finrank (ZMod 2)
        (fixedSpace (overgroupAction n (binaryNormalizer n)) (zpowers (j x))) := by
    rw [←MonoidHom.map_zpowers,←fixedSpace_map_equivariant (automizerRepresentation V)
      (overgroupAction n (binaryNormalizer n)) j e he,LinearEquiv.finrank_map_eq]
  have hodd : Odd (orderOf (j x)) := by
    rw [orderOf_injective j hj,ho]
    exact Nat.Even.sub_odd (Nat.one_le_pow k 2 (by decide))
      (Nat.even_pow.mpr ⟨by decide,by have hn := NeZero.pos n; omega⟩) odd_one
  obtain ⟨_,hdiv⟩ := largeOddFixedSpaceLinearity n (binaryNormalizer n) (j x)
    (j x).property hodd (hm ▸ hlarge)
  rw [←hm] at hdiv
  exact endpoint_arithmetic n _ _ _ _ (NeZero.pos n) hupper hc hsum hfixle hid hdiv

/-- A maximal actor at the endpoint would give an odd similitude fixing
three dimensions of a four-dimensional minus form. This is impossible
on the literal chosen coordinates. -/
private theorem selected_endpoint_not_maximal_actor
    (s : Selected H T M V I k i S) (n : ℕ) [NeZero n]
    (e : Additive V ≃ₗ[ZMod 2] Space n)
    (j : Automizer V →* binaryNormalizer n) (hj : Function.Injective j)
    (he : ∀ a v, e (automizerRepresentation V a v) =
      overgroupAction n (binaryNormalizer n) (j a) (e v))
    (x : Automizer V) (ho : Odd (orderOf x))
    (hx : x ∈ inducedAutomizer V (M ⊓ I))
    (hfixed : automizerFixedGroup V (zpowers x) =
      V ⊓ V.map (MulAut.conj i.val⁻¹).toMonoidHom)
    (ha : rank (inducedAutomizer V
      (V.map (MulAut.conj i.val⁻¹).toMonoidHom ⊓ (pCore 2 I).map I.subtype)) = 4*n)
    (hxf : Module.finrank (ZMod 2)
      (fixedSpace (automizerRepresentation V) (zpowers x)) = 3*n) : False := by
  let A := V.map (MulAut.conj i.val⁻¹).toMonoidHom ⊓ (pCore 2 I).map I.subtype
  let f := (binaryNormalizer n).subtype.comp j
  have hfi : Function.Injective f := (binaryNormalizer n).subtype_injective.comp hj
  let B := (inducedAutomizer V A).map f
  let W := V.map (MulAut.conj i.val⁻¹).toMonoidHom
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.map _
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.of_le (show A ≤ W from inf_le_left)
  let : IsElementaryAbelian 2 (inducedAutomizer V A) :=
    inducedAutomizer_elementary V A (actor_normalizes s)
  let : IsElementaryAbelian 2 B := IsElementaryAbelian.map f
  have hB : B ≤ binaryNormalizer n := by
    rintro _ ⟨a,ha,rfl⟩
    exact (j a).property
  have hBr : rank B = 4*n := (rank_map_injective f hfi _).trans ha
  have hBL := Chapter7.NormalizedSource.NonMathieuHermitian.large_elementary_le_image n B hB
    (by rw [hBr]; have hn := NeZero.pos n; omega)
  have hmap (D : Subgroup (Automizer V)) :
      (fixedSpace (automizerRepresentation V) D).map e.toLinearMap =
        fixedSpace (UnipotentRadicals.ambientAction n) (D.map f) :=
    fixedSpace_map_equivariant _ _ f e he D
  have hX : (zpowers x).map f = zpowers (j x).val := MonoidHom.map_zpowers f x
  have hBX : Module.finrank (ZMod 2)
      (fixedSpace (UnipotentRadicals.ambientAction n) (zpowers (j x).val)) = 3*n := by
    rw [←hX,←hmap,LinearEquiv.finrank_map_eq]
    exact hxf
  have hle : fixedSpace (UnipotentRadicals.ambientAction n) (zpowers (j x).val) ≤
      fixedSpace (UnipotentRadicals.ambientAction n) B := by
    rw [←hX,←hmap,←hmap]
    exact Submodule.map_mono (selected_fixedSpace_le_actor s x hfixed)
  obtain ⟨c,hc | hc⟩ := UnipotentRadicals.maximal_elementary_conjugate n B hBL hBr
  · have hd := (fixedSpaceConjEquiv (UnipotentRadicals.ambientAction n) B
        (binaryActionHom n c)).finrank_eq
    rw [hc,UnipotentRadicals.finrank_point_fixed] at hd
    have hh := Submodule.finrank_mono hle
    rw [hBX,hd] at hh
    have hn := NeZero.pos n
    omega
  · have hBA := (fixedSpaceConjEquiv (UnipotentRadicals.ambientAction n) B
        (binaryActionHom n c)).finrank_eq
    rw [hc,UnipotentRadicals.finrank_plane_fixed] at hBA
    have hnorm : (j x).val ∈ normalizer (B : Set (BinaryAut n)) :=
      (inducedAutomizer V A).le_normalizer_map f
        (mem_map_of_mem f (selected_normalizes_actor s hx))
    have hodd : Odd (orderOf (j x).val) := by
      rwa [Subgroup.orderOf_coe,orderOf_injective j hj]
    have hlin := linear_of_large_fixed_inside_actor n B hBL hBA (j x).val
      (j x).property hodd hnorm hle (by rw [hBX]; have hn := NeZero.pos n; omega)
    obtain ⟨g,hg⟩ := OddExponent.mem_congruenceImage_of_odd_of_isFixedFieldLinear n
      (j x).val (j x).property hodd hlin
    have hgo := OddExponent.odd_orderOf_of_odd_binaryCongruence n g (hg.symm ▸ hodd)
    exact conjugate_plane_no_fixed_rank_three_mul n B c hc g hgo
      (hg.symm ▸ hnorm) (hg.symm ▸ hle) (hg.symm ▸ hBX)

/-- The remaining endpoint has actor rank 3n and torus fixed rank 4n,
without E.2.14(7). Excluding this remaining case still requires its actual
linear-family module or scalar-torus argument. -/
theorem selected_endpoint_actor_rank_three_mul
    (s : Selected H T M V I k i S) (n : ℕ) [NeZero n] (hkn : k = 2*n)
    (e : Additive V ≃ₗ[ZMod 2] Space n)
    (j : Automizer V →* binaryNormalizer n) (hj : Function.Injective j)
    (he : ∀ a v, e (automizerRepresentation V a v) =
      overgroupAction n (binaryNormalizer n) (j a) (e v))
    (x : Automizer V) (ho : orderOf x = 2^k-1)
    (hx : x ∈ inducedAutomizer V (M ⊓ I))
    (hfixed : automizerFixedGroup V (zpowers x) =
      V ⊓ V.map (MulAut.conj i.val⁻¹).toMonoidHom) :
    let A := V.map (MulAut.conj i.val⁻¹).toMonoidHom ⊓ (pCore 2 I).map I.subtype
    rank (inducedAutomizer V A) = 3*n ∧
      Module.finrank (ZMod 2) (fixedSpace (automizerRepresentation V) (zpowers x)) = 4*n := by
  apply (selected_endpoint_actor_rank_alternative s n hkn e j hj he x ho hfixed).resolve_right
  rintro ⟨ha,hxf⟩
  have hodd : Odd (orderOf x) := by
    rw [ho]
    exact Nat.Even.sub_odd (Nat.one_le_pow k 2 (by decide))
      (Nat.even_pow.mpr ⟨by decide,by have hn := NeZero.pos n; omega⟩) odd_one
  exact selected_endpoint_not_maximal_actor s n e j hj he x hodd hx hfixed ha hxf

end CFSG.Quasithin.Chapter8.Section02.HermitianSource
