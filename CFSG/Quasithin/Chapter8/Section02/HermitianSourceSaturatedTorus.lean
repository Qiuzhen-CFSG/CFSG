module
public import CFSG.Quasithin.Chapter8.Section02.HermitianSourceSelection
public import CFSG.Quasithin.Chapter8.Section02.HermitianSourceSelectedTorusBounds
public import Theory.Representation.HermitianTensorThree.ParabolicTorus.Determinant

/-!
# The saturated selected Hermitian actor and its torus

The large-actor bound supplies the geometric premise in the selected-offender
calculation. Together with w >= n, r >= 4n and k <= n, it forces k = w = n,
actor rank 4n and fixed rank 4n, and gives the canonical fixed subgroup.
The selected torus then fixes exactly the same space. The literal plane
conjugacy and fixed-space estimate remove coefficient automorphisms, giving
an odd GL₃ congruence on the original coordinates. In those plane coordinates,
the determinant norm has order 2^n - 1.

The saturation statement includes n = 1. The nontrivial determinant assertion
requires n > 1 and does not itself exclude the ambient source configuration.
Selection, the torus fixed-space identity and the earlier numerical bounds
are explicit inputs here.

Source: Aschbacher–Smith 8.2.3–4 and H.4.4(3,5), printed pp.715–716 and381
(1 March 2004 manuscript, refs/quasithin.pdf).
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open Representation.HermitianTensorThree Representation.HermitianTensorThree.ImageOuter
open Representation.HermitianTensorThree.ParabolicTorus
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter8.Section02.HermitianSource
open ChapterE Offenders.Parabolic Offenders.Parabolic.Construction
variable {G : Type*} [Group G] [Finite G]
  {V : Subgroup G} [IsElementaryAbelian 2 V] {T : Sylow 2 G}
  {H M I : Subgroup G} {k : ℕ} {i : I} {S : Sylow 2 I}

private theorem large_actor_geometry (n : ℕ) [NeZero n]
    (A : Subgroup (binaryNormalizer n)) (hA : IsElementaryTwo A)
    (hr : 3*n ≤ rank A) :
    5*n ≤ fixedCodim (overgroupAction n (binaryNormalizer n)) A := by
  let : IsElementaryAbelian 2 A := hA.2
  exact LargeActors.overgroup_large_elementary_fixedCodim n (binaryNormalizer n) le_rfl A hr

/-- The proved large-actor theorem removes the geometry premise from the
canonical selected-offender calculation. Half-degree one is retained. -/
theorem selected_saturated_fixed_subgroup
    (s : Selected H T M V I k i S) (hT : HypothesisE322 V T)
    (n : ℕ) [NeZero n]
    (e : Additive V ≃ₗ[ZMod 2] Space n)
    (j : Automizer V →* binaryNormalizer n) (hj : Function.Injective j)
    (he : ∀ a v, e (automizerRepresentation V a v) =
      overgroupAction n (binaryNormalizer n) (j a) (e v))
    (hw : (n : ℕ∞) ≤ globalW V T) (hk : k ≤ n)
    (hr : ((4*n : ℕ) : ℕ∞) ≤ globalR V) :
    let A := V.map (MulAut.conj i.val⁻¹).toMonoidHom ⊓ (pCore 2 I).map I.subtype
    let U := V ⊓ centralizer (A : Set G)
    k = n ∧ globalW V T = n ∧ IsWOffenderAt V T i.val⁻¹ ∧
      A = offenderNormalizer V i.val⁻¹ ∧ A ≤ T ∧
      rank (inducedAutomizer V A) = 4*n ∧ rank U = 4*n ∧
      U = V ⊓ V.map (MulAut.conj i.val⁻¹).toMonoidHom ∧
      (U.subgroupOf T).Normal ∧ (T : Subgroup G) ≤ normalizer (U : Set G) ∧
      I ≤ centralizer (U : Set G) ∧ globalR V ≤ ((5*n : ℕ) : ℕ∞) := by
  obtain ⟨hkn,hew,hOff,hAT,hA,_,ha,hu,hr',_,hU,hn,hN,hI⟩ :=
    selected_hermitian_fixed_subgroup s hT n e j hj he
      (large_actor_geometry n) hw hk hr
  rw [hA] at hAT ha hu hU hn hN hI
  exact ⟨hkn,hew,hOff,hA.symm,hAT,ha,hu,hU,hn,hN,hI,hr'⟩

private theorem fixedGroup_rank (X : Subgroup (Automizer V)) :
    rank (automizerFixedGroup V X) =
      Module.finrank (ZMod 2) (fixedSpace (automizerRepresentation V) X) := by
  rw [rank,automizerFixedGroup,card_map_of_injective V.subtype_injective]
  change Nat.log 2 (Nat.card (fixedSpace (automizerRepresentation V) X)) = _
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod,
    Nat.log_pow Nat.one_lt_two]

omit [Finite G] in
private theorem fixedSpace_eq_of_fixedGroup_eq
    (X Y : Subgroup (Automizer V))
    (h : automizerFixedGroup V X = automizerFixedGroup V Y) :
    fixedSpace (automizerRepresentation V) X = fixedSpace (automizerRepresentation V) Y := by
  have hm (B : Subgroup (Automizer V)) (v : Additive V) :
      v ∈ fixedSpace (automizerRepresentation V) B ↔
        v.toMul.val ∈ automizerFixedGroup V B := by
    constructor
    · intro hv
      exact ⟨v.toMul,hv,rfl⟩
    · rintro ⟨w,hw,he⟩
      have hwv : w = v.toMul := Subtype.ext he
      subst w
      exact hw
  ext v
  rw [hm,hm,h]

/-- Once the selected actor saturates, its torus has exactly the same fixed
space. On the original coordinates it is an odd congruence, with no
coefficient automorphism. No assertion about its determinant is made. -/
theorem selected_saturated_torus_congruence
    (s : Selected H T M V I k i S) (hT : HypothesisE322 V T)
    (n : ℕ) [NeZero n]
    (e : Additive V ≃ₗ[ZMod 2] Space n)
    (j : Automizer V →* binaryNormalizer n) (hj : Function.Injective j)
    (he : ∀ a v, e (automizerRepresentation V a v) =
      overgroupAction n (binaryNormalizer n) (j a) (e v))
    (hw : (n : ℕ∞) ≤ globalW V T) (hk : k ≤ n)
    (hr : ((4*n : ℕ) : ℕ∞) ≤ globalR V)
    (x : Automizer V) (hx : x ∈ inducedAutomizer V (M ⊓ I))
    (ho : orderOf x = 2^k-1)
    (hfixed : automizerFixedGroup V (zpowers x) =
      V ⊓ V.map (MulAut.conj i.val⁻¹).toMonoidHom) :
    let A := V.map (MulAut.conj i.val⁻¹).toMonoidHom ⊓ (pCore 2 I).map I.subtype
    let f := (binaryNormalizer n).subtype.comp j
    fixedSpace (automizerRepresentation V) (zpowers x) =
        fixedSpace (automizerRepresentation V) (inducedAutomizer V A) ∧
      Module.finrank (ZMod 2) (fixedSpace (automizerRepresentation V) (zpowers x)) = 4*n ∧
      (∃ c : Cover n, ((inducedAutomizer V A).map f).map
        (MulAut.conj (binaryActionHom n c)).toMonoidHom = UnipotentRadicals.plane n) ∧
      IsFixedFieldLinear n (j x).val ∧
      ∃ g : Matrix.GeneralLinearGroup (Fin 3) (E n),
        binaryCongruence n g = (j x).val ∧ Odd (orderOf g) := by
  let A := V.map (MulAut.conj i.val⁻¹).toMonoidHom ⊓ (pCore 2 I).map I.subtype
  obtain ⟨hkn,hew,hOff,hA,hAT,ha,hu,hU,_,_,_,_⟩ :=
    selected_saturated_fixed_subgroup s hT n e j hj he hw hk hr
  have hAN : A ≤ normalizer (V : Set G) := hAT.trans hT.normalizes
  have hfixed' : automizerFixedGroup V (zpowers x) =
      automizerFixedGroup V (inducedAutomizer V A) := by
    rw [automizerFixedGroup_induced V A hAN,hfixed]
    exact hU.symm
  have hspace := fixedSpace_eq_of_fixedGroup_eq _ _ hfixed'
  have haf : Module.finrank (ZMod 2)
      (fixedSpace (automizerRepresentation V) (inducedAutomizer V A)) = 4*n := by
    rw [←fixedGroup_rank,automizerFixedGroup_induced V A hAN]
    exact hu
  have hxf : Module.finrank (ZMod 2)
      (fixedSpace (automizerRepresentation V) (zpowers x)) = 4*n := by rw [hspace,haf]
  let f := (binaryNormalizer n).subtype.comp j
  let B := (inducedAutomizer V A).map f
  let : IsElementaryAbelian 2 (inducedAutomizer V A) := by
    change A = offenderNormalizer V i.val⁻¹ at hA
    rw [hA]
    exact offender_inducedAutomizer_elementary V i.val⁻¹
  let : IsElementaryAbelian 2 B := IsElementaryAbelian.map f
  have hBN : B ≤ binaryNormalizer n := by
    rintro _ ⟨a,ha,rfl⟩
    exact (j a).property
  have hBr : rank B = 4*n :=
    (rank_map_injective f ((binaryNormalizer n).subtype_injective.comp hj) _).trans ha
  have hBL : B ≤ binaryImage n :=
    Chapter7.NormalizedSource.NonMathieuHermitian.large_elementary_le_image n B hBN
      (by rw [hBr]; have hn := NeZero.pos n; omega)
  have hm (D : Subgroup (Automizer V)) :
      (fixedSpace (automizerRepresentation V) D).map e.toLinearMap =
        fixedSpace (UnipotentRadicals.ambientAction n) (D.map f) :=
    fixedSpace_map_equivariant _ _ f e he D
  have hBf : Module.finrank (ZMod 2)
      (fixedSpace (UnipotentRadicals.ambientAction n) B) = 4*n := by
    rw [←hm,LinearEquiv.finrank_map_eq]
    exact haf
  have hX : (zpowers x).map f = zpowers (j x).val := MonoidHom.map_zpowers f x
  have hBspace : fixedSpace (UnipotentRadicals.ambientAction n) (zpowers (j x).val) =
      fixedSpace (UnipotentRadicals.ambientAction n) B := by
    rw [←hX,←hm,←hm,hspace]
  have hnorm : (j x).val ∈ normalizer (B : Set (BinaryAut n)) :=
    (inducedAutomizer V A).le_normalizer_map f
      (mem_map_of_mem f (selected_normalizes_actor s hx))
  have hodd : Odd (orderOf (j x).val) := by
    rw [Subgroup.orderOf_coe,orderOf_injective j hj,ho]
    exact Nat.Even.sub_odd (Nat.one_le_pow k 2 (by decide))
      (Nat.even_pow.mpr ⟨by decide,by have hn := NeZero.pos n; omega⟩) odd_one
  have hlin := linear_of_large_fixed_inside_actor n B hBL hBf (j x).val
    (j x).property hodd hnorm hBspace.le
    (by rw [hBspace,hBf]; have hn := NeZero.pos n; omega)
  obtain ⟨g,hg⟩ := OddExponent.mem_congruenceImage_of_odd_of_isFixedFieldLinear n
    (j x).val (j x).property hodd hlin
  exact ⟨hspace,hxf,
    Chapter7.NormalizedSource.NonMathieuHermitian.saturated_actor_plane n B hBN hBr hBf,
    hlin,g,hg,OddExponent.odd_orderOf_of_odd_binaryCongruence n g (hg.symm ▸ hodd)⟩

/-- In plane coordinates the actual selected torus forces determinant
norm different from one. Thus the final ambient argument must rule out
this scalar contribution; coefficient linearity alone does not suffice. -/
theorem selected_saturated_torus_det_norm_order
    (s : Selected H T M V I k i S) (hT : HypothesisE322 V T)
    (n : ℕ) [NeZero n] (hn : 1 < n)
    (e : Additive V ≃ₗ[ZMod 2] Space n)
    (j : Automizer V →* binaryNormalizer n) (hj : Function.Injective j)
    (he : ∀ a v, e (automizerRepresentation V a v) =
      overgroupAction n (binaryNormalizer n) (j a) (e v))
    (hw : (n : ℕ∞) ≤ globalW V T) (hk : k ≤ n)
    (hr : ((4*n : ℕ) : ℕ∞) ≤ globalR V)
    (x : Automizer V) (hx : x ∈ inducedAutomizer V (M ⊓ I))
    (ho : orderOf x = 2^k-1)
    (hfixed : automizerFixedGroup V (zpowers x) =
      V ⊓ V.map (MulAut.conj i.val⁻¹).toMonoidHom) :
    let A := V.map (MulAut.conj i.val⁻¹).toMonoidHom ⊓ (pCore 2 I).map I.subtype
    ∃ (c : Cover n) (g : Matrix.GeneralLinearGroup (Fin 3) (E n)),
      ((inducedAutomizer V A).map ((binaryNormalizer n).subtype.comp j)).map
        (MulAut.conj (binaryActionHom n c)).toMonoidHom = UnipotentRadicals.plane n ∧
      binaryCongruence n g = (MulAut.conj (binaryActionHom n c)) (j x).val ∧
      Odd (orderOf g) ∧ orderOf (g.val.det * sigma n g.val.det) = 2^n-1 ∧
      g.val.det * sigma n g.val.det ≠ 1 := by
  obtain ⟨hkn,_,_,_,_⟩ := selected_hermitian_parameters s hT n hw hk
  obtain ⟨hspace,_,⟨c,hc⟩,_,g,hg,hgo⟩ :=
    selected_saturated_torus_congruence s hT n e j hj he hw hk hr x hx ho hfixed
  let A := V.map (MulAut.conj i.val⁻¹).toMonoidHom ⊓ (pCore 2 I).map I.subtype
  let f := (binaryNormalizer n).subtype.comp j
  let B := (inducedAutomizer V A).map f
  let u := binaryActionHom n c
  let z := (MulAut.conj u).toMonoidHom
  let g' := (MulAut.conj (Matrix.SpecialLinearGroup.toGL c)) g
  have hg' : binaryCongruence n g' = z (j x).val := by
    change binaryCongruence n (Matrix.SpecialLinearGroup.toGL c * g *
      (Matrix.SpecialLinearGroup.toGL c)⁻¹) = _
    rw [map_mul,map_mul,map_inv,binaryCongruence_toGL,hg]
    rfl
  have hm (Y : Subgroup (Automizer V)) := fixedSpace_map_equivariant
    (automizerRepresentation V) (UnipotentRadicals.ambientAction n) f e he Y
  have hz : (zpowers x).map f = zpowers (j x).val := MonoidHom.map_zpowers f x
  have hBspace : fixedSpace (UnipotentRadicals.ambientAction n) B =
      fixedSpace (UnipotentRadicals.ambientAction n) (zpowers (j x).val) := by
    rw [←hz,←hm,←hm,hspace]
  have hez (a : BinaryAut n) (v : Space n) :
      u (UnipotentRadicals.ambientAction n a v) =
        UnipotentRadicals.ambientAction n (z a) (u v) := by
    change u (a v) = u (a (u.symm (u v)))
    rw [u.symm_apply_apply]
  have hmz (Y : Subgroup (BinaryAut n)) := fixedSpace_map_equivariant
    (UnipotentRadicals.ambientAction n) (UnipotentRadicals.ambientAction n) z u hez Y
  have hplane : fixedSpace (UnipotentRadicals.ambientAction n) (UnipotentRadicals.plane n) =
      fixedSpace (UnipotentRadicals.ambientAction n) (zpowers (binaryCongruence n g')) := by
    rw [hg',←MonoidHom.map_zpowers,←hc,←hmz,←hmz,hBspace]
  have hord : orderOf (binaryCongruence n g') = 2^n-1 := by
    rw [hg',orderOf_injective z (MulAut.conj u).injective,Subgroup.orderOf_coe,
      orderOf_injective j hj,ho,hkn]
  have hfix : ∀ X ∈ fixedSpace (UnipotentRadicals.ambientAction n) (UnipotentRadicals.plane n),
      binaryCongruence n g' X = X := by
    intro X hX
    rw [hplane] at hX
    exact (mem_fixedSpace_zpowers_iff _ _ _).mp hX
  refine ⟨c,g',hc,hg',?_,plane_fixed_det_norm_order n g' hfix hord,?_⟩
  · exact (orderOf_injective (MulAut.conj (Matrix.SpecialLinearGroup.toGL c)).toMonoidHom
      (MulAut.conj (Matrix.SpecialLinearGroup.toGL c)).injective g).symm ▸ hgo
  · intro hdet
    exact plane_no_split_torus_of_det_norm_one n g' hfix hdet hord hn

end CFSG.Quasithin.Chapter8.Section02.HermitianSource
