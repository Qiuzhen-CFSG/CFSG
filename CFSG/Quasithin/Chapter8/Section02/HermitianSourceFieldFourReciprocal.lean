module
public import CFSG.Quasithin.Chapter8.Section02.HermitianSourceFieldFourClosure
public import CFSG.Quasithin.ChapterE.Section04.GenerationSetup
public import Theory.Representation.BinaryOffender.QuadraticRatioTransport

/-!
# Reciprocal normalizers in the field-four zero-closure configuration

A third-family actor in the nine-dimensional Hermitian module is the plane
radical: its central root excludes the point radical, and its fixed subgroup
has rank four. The saturated-plane theorem makes that fixed subgroup normal
in the original Sylow subgroup.

On the returning conjugate, the reverse normalizer acts quadratically and
fixes a subgroup of rank five. An outer elementary actor of rank at least two
fixes at most four dimensions, while an inner quadratic actor has rank at most
one. The reverse image therefore has rank at most one; its rank-four kernel
bounds the reverse normalizer by five. Joining the original module to the
rank-five forward kernel also gives an elementary subgroup of rank at least
ten in the original Sylow subgroup.

These are consequences of the remaining zero-closure configuration, not its
exclusion. The Chapter 12 application keeps the original module and Sylow.
The ambient field-four argument through 8.2.13 remains to be completed.

Source: Aschbacher--Smith E.3.28--32, H.4.4--5 and 7.5.6,
printed pp.237--238,381--382,701; compare the canonical fixed subgroup in
8.2.5, pp.716--717, refs/quasithin.pdf (1 March 2004 manuscript).
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open Representation.HermitianTensorThree Representation.HermitianTensorThree.ImageOuter
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter8.Section02.HermitianSource
open ChapterE

private theorem point_not_third_family :
    UnipotentRadicals.point 1 ∉ fixedSpaceFamily (UnipotentRadicals.ambientAction 1) 3 := by
  intro h
  let R := (Matrix.PSL3Even.UnipotentGeometry.Z (E 1)).map
    (UnipotentRadicals.unipotentHom 1)
  have hRpoint : R ≤ UnipotentRadicals.point 1 := by
    apply map_mono
    intro x hx
    exact (Matrix.PSL3Even.UnipotentGeometry.mem_V₁ _ _).mpr
      ((Matrix.PSL3Even.UnipotentGeometry.mem_Z _ _).mp hx).2
  have hRplane : R ≤ UnipotentRadicals.plane 1 := by
    apply map_mono
    intro x hx
    exact (Matrix.PSL3Even.UnipotentGeometry.mem_V₂ _ _).mpr
      ((Matrix.PSL3Even.UnipotentGeometry.mem_Z _ _).mp hx).1
  have hr : R.relIndex (UnipotentRadicals.point 1) = 4 := by
    change ((Matrix.PSL3Even.UnipotentGeometry.Z (E 1)).map _).relIndex
      ((Matrix.PSL3Even.UnipotentGeometry.V₁ (E 1)).map _) = 4
    rw [Subgroup.relIndex_map_map_of_injective _ _
      (UnipotentRadicals.unipotentHom_injective 1)]
    have he := Subgroup.relIndex_mul_relIndex (⊥ : Subgroup (Matrix.PSL3Even.UnipotentGeometry.U (E 1)))
      (Matrix.PSL3Even.UnipotentGeometry.Z (E 1))
      (Matrix.PSL3Even.UnipotentGeometry.V₁ (E 1)) bot_le
      (show Matrix.PSL3Even.UnipotentGeometry.Z (E 1) ≤
        Matrix.PSL3Even.UnipotentGeometry.V₁ (E 1) from fun x hx =>
          (Matrix.PSL3Even.UnipotentGeometry.mem_V₁ _ _).mpr
            ((Matrix.PSL3Even.UnipotentGeometry.mem_Z _ _).mp hx).2)
    rw [relIndex_bot_left,relIndex_bot_left,Matrix.PSL3Even.UnipotentGeometry.card_Z,
      Matrix.PSL3Even.UnipotentGeometry.card_V₁,card_E] at he
    norm_num at he ⊢
    omega
  have he := h.2.2 R hRpoint (by rw [hr]; decide)
  have hd := Submodule.finrank_mono
    (BinaryOffender.fixedSpace_antitone (UnipotentRadicals.ambientAction 1) hRplane)
  rw [←he,UnipotentRadicals.finrank_point_fixed,
    UnipotentRadicals.finrank_plane_fixed] at hd
  omega

variable {G : Type*} [Group G] [Finite G]
  (V : Subgroup G) [IsElementaryAbelian 2 V]
  (e : Additive V ≃ₗ[ZMod 2] Space 1)
  (j : Automizer V →* binaryNormalizer 1) (hj : Function.Injective j)
  (he : ∀ a v, e (automizerRepresentation V a v) =
    overgroupAction 1 (binaryNormalizer 1) (j a) (e v))

include hj he in
/-- Every third-family actor is a cover-conjugate of the literal plane
radical, with rank four and fixed codimension five. -/
theorem field_four_third_family_plane
    (A : Subgroup (Automizer V))
    (hA : A ∈ fixedSpaceFamily (automizerRepresentation V) 3) :
    rank A = 4 ∧ fixedCodim (automizerRepresentation V) A = 5 ∧
      ∃ c : Cover 1, (A.map ((binaryNormalizer 1).subtype.comp j)).map
        (MulAut.conj (binaryActionHom 1 c)).toMonoidHom = UnipotentRadicals.plane 1 := by
  obtain ⟨hr,hi⟩ := field_four_fixed_family_three_rank V e j hj he A hA
  let f := (binaryNormalizer 1).subtype.comp j
  have hf : Function.Injective f := (binaryNormalizer 1).subtype_injective.comp hj
  let : IsElementaryAbelian 2 A := hA.2.1.2
  let : IsElementaryAbelian 2 (A.map f) := IsElementaryAbelian.map _
  have hfam := fixedSpaceFamily_map_of_equivariant (automizerRepresentation V)
    (UnipotentRadicals.ambientAction 1) f hf e he hA
  obtain ⟨c,hc⟩ := UnipotentRadicals.maximal_elementary_conjugate 1 (A.map f) hi
    (by rw [rank_map_injective f hf,hr])
  have hp : (A.map f).map (MulAut.conj (binaryActionHom 1 c)).toMonoidHom =
      UnipotentRadicals.plane 1 := by
    rcases hc with hc | hc
    · have hh := ChapterE.ValueBound.fixedSpaceFamily_conjugationInvariant
        (UnipotentRadicals.ambientAction 1) 3 (A.map f) hfam (binaryActionHom 1 c)
      rw [hc] at hh
      exact (point_not_third_family hh).elim
    · exact hc
  have hdim := (fixedSpaceConjEquiv (UnipotentRadicals.ambientAction 1)
    (A.map f) (binaryActionHom 1 c)).finrank_eq
  rw [hp,UnipotentRadicals.finrank_plane_fixed] at hdim
  have hsum := fixedCodim_add_finrank (UnipotentRadicals.ambientAction 1) (A.map f)
  rw [hdim,finrank_binary] at hsum
  have hcod := fixedCodim_map_equivariant (automizerRepresentation V)
    (UnipotentRadicals.ambientAction 1) f e he A
  exact ⟨hr,by omega,c,hp⟩

private theorem binary_rank_add (W U : Subgroup G) [IsElementaryAbelian 2 W]
    (hUW : U ≤ W) : rank W = subgroupCorank W U + rank U := by
  simpa only [subgroupCorank,relIndex_bot_left,rank] using
    (offender_corank_add (W := W) (A := U) bot_le hUW)

include hj he in
/-- The rank-four fixed subgroup of a third-family actor is normalized
by the original Sylow subgroup. -/
theorem field_four_third_family_fixed_normal
    (T : Sylow 2 G) (hT : HypothesisE322 V T)
    (W : Subgroup G) (hWT : W ≤ T)
    (hW : inducedAutomizer V W ∈ fixedSpaceFamily (automizerRepresentation V) 3) :
    rank (V ⊓ centralizer (W : Set G)) = 4 ∧
      (T : Subgroup G) ≤ normalizer (V ⊓ centralizer (W : Set G) : Set G) := by
  have hWN := hWT.trans hT.normalizes
  obtain ⟨ha,hcod,_⟩ := field_four_third_family_plane V e j hj he _ hW
  have hdim : rank V = 9 := by
    rw [rank,show Nat.card V = Nat.card (Additive V) from rfl,
      Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod,
      e.finrank_eq,finrank_binary,Nat.log_pow Nat.one_lt_two]
  have hcor : subgroupCorank V (V ⊓ centralizer (W : Set G)) = 5 := by
    rwa [fixedCodim_inducedAutomizer V W hWN] at hcod
  have hu : rank (V ⊓ centralizer (W : Set G)) = 4 := by
    have hh := binary_rank_add V (V ⊓ centralizer (W : Set G)) inf_le_left
    omega
  refine ⟨hu,?_⟩
  let A := inducedAutomizer V W
  let P := inducedAutomizer V T
  let f := (binaryNormalizer 1).subtype.comp j
  have hf : Function.Injective f := (binaryNormalizer 1).subtype_injective.comp hj
  let : IsElementaryAbelian 2 A := hW.2.1.2
  let : IsElementaryAbelian 2 (A.map f) := IsElementaryAbelian.map _
  have hAr : rank (A.map f) = 4*1 := by rw [rank_map_injective f hf,ha]
  have hAf : Module.finrank (ZMod 2)
      (fixedSpace (UnipotentRadicals.ambientAction 1) (A.map f)) = 4*1 := by
    have hc := fixedCodim_map_equivariant (automizerRepresentation V)
      (UnipotentRadicals.ambientAction 1) f e he A
    have hd := fixedCodim_add_finrank (UnipotentRadicals.ambientAction 1) (A.map f)
    rw [←hc,hcod,finrank_binary] at hd
    omega
  have hp : IsPGroup 2 P := T.2.comap_subtype.map _
  have hAP : A ≤ P := map_mono (comap_mono hWT)
  have hPN : P.map f ≤ binaryNormalizer 1 := by
    rintro _ ⟨a,_,rfl⟩
    exact (j a).property
  have hN := Chapter7.NormalizedSource.NonMathieuHermitian.saturated_actor_normalized 1
    (P.map f) (hp.map f) hPN (A.map f) (map_mono hAP) hAr hAf
  have hN' : P ≤ normalizer (A : Set (Automizer V)) := by
    intro a haP
    apply mem_normalizer_iff_map_conj_eq.mpr
    apply Subgroup.map_injective hf
    change (A.map (MulAut.conj a).toMonoidHom).map f = A.map f
    rw [map_map]
    have heq : f.comp (MulAut.conj a).toMonoidHom =
        (MulAut.conj (f a)).toMonoidHom.comp f := by
      ext b
      simp [MulAut.conj_apply]
    rw [heq,←map_map]
    exact mem_normalizer_iff_map_conj_eq.mp (hN (mem_map_of_mem f haP))
  exact Offenders.fixed_normalized_of_image_normalized V W T hWN hT.normalizes hN'

include hj he in
/-- A quadratic elementary actor fixing at least five dimensions has
induced rank at most one in the field-four Hermitian module. -/
theorem field_four_quadratic_actor_rank_le_one_of_fixed_five
    (A : Subgroup G) [IsElementaryAbelian 2 A]
    (hAN : A ≤ normalizer (V : Set G))
    (hfix : 5 ≤ rank (V ⊓ centralizer (A : Set G)))
    (hq : ⁅⁅V,A⁆,A⁆ = ⊥) :
    rank (inducedAutomizer V A) ≤ 1 := by
  by_contra! hr
  let I := inducedAutomizer V A
  let f := (binaryNormalizer 1).subtype.comp j
  have hf : Function.Injective f := (binaryNormalizer 1).subtype_injective.comp hj
  let : IsElementaryAbelian 2 I := inducedAutomizer_elementary V A hAN
  let : IsElementaryAbelian 2 (I.map f) := IsElementaryAbelian.map _
  have hIr : 1 < rank (I.map f) := by rwa [rank_map_injective f hf]
  by_cases hi : I.map f ≤ binaryImage 1
  · have hqI : IsQuadratic (automizerRepresentation V) I := by
      rintro a ⟨a₀,ha₀,rfl⟩ b ⟨b₀,hb₀,rfl⟩ v
      have happ (x : normalizer (V : Set G)) (u : Additive V) :
          ((automizerRepresentation V (V.normalizerMonoidHom.rangeRestrict x) u).toMul : G) =
            (x : G) * (u.toMul : G) * (x : G)⁻¹ := rfl
      apply Additive.toMul.injective
      apply Subtype.ext
      simp only [happ,toMul_sub,div_eq_mul_inv]
      change (a₀ : G) * ((b₀ : G) * (v.toMul : G) * (b₀ : G)⁻¹ * (v.toMul : G)⁻¹) *
        (a₀ : G)⁻¹ = (b₀ : G) * (v.toMul : G) * (b₀ : G)⁻¹ * (v.toMul : G)⁻¹
      have hc : ⁅(b₀ : G),(v.toMul : G)⁆ ∈ centralizer (A : Set G) := by
        apply (commutator_eq_bot_iff_le_centralizer.mp hq)
        rw [commutator_comm V A]
        exact commutator_mem_commutator hb₀ v.toMul.property
      have hh := hc (a₀ : G) ha₀
      simpa only [commutatorElement_def] using (mul_inv_eq_iff_eq_mul.mpr hh)
    have hq' := quadratic_map_equivariant (automizerRepresentation V)
      (UnipotentRadicals.ambientAction 1) f e he hqI
    have hb := Chapter7.NormalizedSource.NonMathieuHermitian.inner_quadratic_rank_le 1
      (I.map f) ⟨fun hz => by simp [hz] at hIr,inferInstance⟩ hi hq'
    omega
  · have hd := LargeActors.outer_fixed_rank_le 1 (I.map f)
      (by rintro _ ⟨a,_,rfl⟩; exact (j a).property) hi hIr
    have hc := fixedCodim_add_finrank (UnipotentRadicals.ambientAction 1) (I.map f)
    rw [finrank_binary,←fixedCodim_map_equivariant (automizerRepresentation V)
      (UnipotentRadicals.ambientAction 1) f e he I,
      fixedCodim_inducedAutomizer V A hAN] at hc
    have hdim : rank V = 9 := by
      rw [rank,show Nat.card V = Nat.card (Additive V) from rfl,
        Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod,
        e.finrank_eq,finrank_binary,Nat.log_pow Nat.one_lt_two]
    have hadd := binary_rank_add V _ (show V ⊓ centralizer (A : Set G) ≤ V from inf_le_left)
    omega

include hj he in
/-- Reciprocal quadraticity bounds the actual reverse normalizer by five,
retaining the original action through ambient conjugation. -/
theorem field_four_reverse_normalizer_rank
    (g : G) (hWN : V.map (MulAut.conj g).toMonoidHom ≤ normalizer (V : Set G))
    (hfix : rank (V ⊓ centralizer
      (V.map (MulAut.conj g).toMonoidHom : Set G)) = 4)
    (hker : 5 ≤ rank (V.map (MulAut.conj g).toMonoidHom ⊓ centralizer (V : Set G))) :
    rank (V ⊓ normalizer (V.map (MulAut.conj g).toMonoidHom : Set G)) ≤ 5 := by
  let W := V.map (MulAut.conj g).toMonoidHom
  let A := V ⊓ normalizer (W : Set G)
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.map _
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.of_le (show A ≤ V from inf_le_left)
  let c := automizerModuleEquiv V (MulAut.conj g)
  let a := automizerMapEquiv V (MulAut.conj g)
  have he' : ∀ x v, (c.symm.trans e) (automizerRepresentation W x v) =
      overgroupAction 1 (binaryNormalizer 1) ((j.comp a.symm.toMonoidHom) x)
        ((c.symm.trans e) v) := by
    intro x v
    have hc : c.symm (automizerRepresentation W x v) =
        automizerRepresentation V (a.symm x) (c.symm v) := by
      apply c.injective
      rw [c.apply_symm_apply]
      have hh := automizerRepresentation_equivariant V (MulAut.conj g) (a.symm x) (c.symm v)
      change c _ = automizerRepresentation W (a (a.symm x)) (c (c.symm v)) at hh
      rw [a.apply_symm_apply,c.apply_symm_apply] at hh
      exact hh.symm
    exact (congrArg e hc).trans (he (a.symm x) (c.symm v))
  have hlarge : 5 ≤ rank (W ⊓ centralizer (A : Set G)) :=
    hker.trans (Nat.log_mono_right (Nat.card_le_card_of_injective
      (inclusion (inf_le_inf_left W (centralizer_le (show A ≤ V from inf_le_left))))
      (inclusion_injective _)))
  have hq : ⁅⁅W,A⁆,A⁆ = ⊥ := by
    have hh := reverse_normalizer_quadratic_on_offender V g
    have heq : offenderNormalizer V g = W := inf_eq_left.mpr hWN
    rwa [heq] at hh
  have hr := field_four_quadratic_actor_rank_le_one_of_fixed_five W (c.symm.trans e)
    (j.comp a.symm.toMonoidHom) (hj.comp a.symm.injective) he' A inf_le_right hlarge hq
  have hK : A ⊓ centralizer (W : Set G) = V ⊓ centralizer (W : Set G) := by
    apply le_antisymm (inf_le_inf_right _ inf_le_left)
    exact le_inf (le_inf inf_le_left
      (inf_le_right.trans (Subgroup.centralizer_le_normalizer _))) inf_le_right
  have hc := rank_inducedAutomizer W A (show A ≤ normalizer (W : Set G) from inf_le_right)
  have hadd := binary_rank_add A _ (show A ⊓ centralizer (W : Set G) ≤ A from inf_le_left)
  rw [←hc,hK] at hadd
  change rank A ≤ 5
  change rank (V ⊓ centralizer (W : Set G)) = 4 at hfix
  omega

private theorem card_eq_pow_rank (A : Subgroup G) [IsElementaryAbelian 2 A] :
    Nat.card A = 2 ^ rank A := by
  obtain ⟨k,hk⟩ := (IsElementaryAbelian.isPGroup 2 A).exists_card_eq
  rw [rank,hk,Nat.log_pow Nat.one_lt_two]

private theorem elementary_enlargement
    (W : Subgroup G) [IsElementaryAbelian 2 W]
    (hV : rank V = 9) (hfix : rank (V ⊓ centralizer (W : Set G)) = 4)
    (hker : rank (W ⊓ centralizer (V : Set G)) = 5) :
    let J := V ⊔ (W ⊓ centralizer (V : Set G))
    IsElementaryAbelian 2 J ∧ 10 ≤ rank J := by
  let K := W ⊓ centralizer (V : Set G)
  let : IsElementaryAbelian 2 K := IsElementaryAbelian.of_le (show K ≤ W from inf_le_left)
  let : IsElementaryAbelian 2 (V ⊔ K : Subgroup G) := IsElementaryAbelian.sup_of_le_centralizer inf_le_right
  let : IsElementaryAbelian 2 (V ⊓ K : Subgroup G) := IsElementaryAbelian.of_le (show V ⊓ K ≤ V from inf_le_left)
  have hle : V ⊓ K ≤ V ⊓ centralizer (W : Set G) :=
    le_inf inf_le_left ((inf_le_right.trans inf_le_left).trans W.le_centralizer)
  have hb : rank (V ⊓ K) ≤ 4 :=
    (Nat.log_mono_right (Nat.card_le_card_of_injective (inclusion hle)
      (inclusion_injective hle))).trans_eq hfix
  have hc := card_mul_eq_card_inf_mul_card_sup_of_normalizes V K
    ((show K ≤ centralizer (V : Set G) from inf_le_right).trans
      (Subgroup.centralizer_le_normalizer _))
  rw [card_eq_pow_rank V,card_eq_pow_rank K,card_eq_pow_rank (V ⊓ K),
    card_eq_pow_rank (V ⊔ K),←pow_add,←pow_add] at hc
  have hh := Nat.pow_right_injective (by decide : 2 ≤ 2) hc
  change rank K = 5 at hker
  change IsElementaryAbelian 2 (V ⊔ K : Subgroup G) ∧ 10 ≤ rank (V ⊔ K)
  exact ⟨inferInstance,by omega⟩

include hj he in
/-- Zero weak closure forces a Sylow elementary rank of at least ten and
a returning conjugate with a Sylow-normal fixed subgroup of rank four,
forward kernel of rank five, and reverse normalizer of rank at most five. -/
theorem field_four_zero_reciprocal_geometry
    (T : Sylow 2 G) (hT : HypothesisE322 V T)
    (hFF : ¬ IsFFModule (automizerRepresentation V))
    (hr : 3 ≤ globalR V) (hm : 3 ≤ localM V) (hw : globalW V T = 0) :
    10 ≤ primeRank 2 T ∧
      ∃ g : G, V.map (MulAut.conj g).toMonoidHom ≤ T ∧ IsWOffenderAt V T g ∧
        rank (V ⊓ centralizer (V.map (MulAut.conj g).toMonoidHom : Set G)) = 4 ∧
        (T : Subgroup G) ≤ normalizer
          (V ⊓ centralizer (V.map (MulAut.conj g).toMonoidHom : Set G) : Set G) ∧
        rank (V.map (MulAut.conj g).toMonoidHom ⊓ centralizer (V : Set G)) = 5 ∧
        rank (V ⊓ normalizer (V.map (MulAut.conj g).toMonoidHom : Set G)) ≤ 5 ∧
        ¬ V ≤ normalizer (V.map (MulAut.conj g).toMonoidHom : Set G) := by
  obtain ⟨_,hs,g,hg,hOff,_,_,hk⟩ := field_four_zero_weak_closure V e j hj he
    T hT hFF hr hm hw
  let W := V.map (MulAut.conj g).toMonoidHom
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.map _
  have hA : offenderNormalizer V g = W := inf_eq_left.mpr (hg.trans hT.normalizes)
  have hf := (offender_fixedSpaceFamily_of_lt_globalS hOff (by rw [hw,hs]; decide)).2
  rw [hw,hs,hA] at hf
  obtain ⟨hfix,hN⟩ := field_four_third_family_fixed_normal V e j hj he T hT W hg hf
  have hrev := field_four_reverse_normalizer_rank V e j hj he g (hg.trans hT.normalizes) hfix hk.ge
  have hdim : rank V = 9 := by
    rw [rank,show Nat.card V = Nat.card (Additive V) from rfl,
      Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod,
      e.finrank_eq,finrank_binary,Nat.log_pow Nat.one_lt_two]
  have hnot : ¬ V ≤ normalizer (W : Set G) := by
    intro hh
    rw [inf_eq_left.mpr hh,hdim] at hrev
    omega
  let J := V ⊔ (W ⊓ centralizer (V : Set G))
  obtain ⟨hJ,hJr⟩ := elementary_enlargement V W hdim hfix hk
  let : IsElementaryAbelian 2 J := hJ
  have hJT : J ≤ T := sup_le hT.le_sylow (inf_le_left.trans hg)
  let : IsElementaryAbelian 2 (J.subgroupOf T) := IsElementaryAbelian.subgroupOf hJT
  have hJrank : rank (J.subgroupOf T) = rank J :=
    congrArg (Nat.log 2) (Nat.card_congr (subgroupOfEquivOfLe hJT).toEquiv)
  have hTbound := offender_rank_le_primeRank (J.subgroupOf T)
  rw [hJrank] at hTbound
  exact ⟨hJr.trans hTbound,g,hg,hOff,hfix,hN,hk,hrev,hnot⟩

end CFSG.Quasithin.Chapter8.Section02.HermitianSource
