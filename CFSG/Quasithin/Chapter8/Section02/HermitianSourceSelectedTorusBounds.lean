module
public import CFSG.Quasithin.Chapter8.Section02.HermitianSourceSelectedTorusRanks
public import CFSG.Quasithin.Chapter7.NormalizedSource.NonMathieuHermitianRadicals
public import Theory.Representation.HermitianTensorThree.UnipotentRadicals.LargeActors
public import Theory.Representation.HermitianTensorThree.ParabolicTorus.PlaneFixed
public import CFSG.Quasithin.Chapter8.Section02.HermitianSourceTorus

/-!
# Rank bounds for the selected Hermitian torus

The central intersection Z is centralized by I, and I cannot normalize V:
otherwise V would be a normal two-subgroup of I, contrary to the positive
rank of its image modulo O₂(I). Thus Z witnesses r ≤ k + rank(Aut_A(V)).
For k < 2n and r ≥ 4n, the selected actor has rank greater than 2n.
The inner and outer Hermitian fixed-space bounds then give codimension
at least 5n without assuming that this actor already attains w.

Together with the constructed torus's fixed-space identity, its parabolic
and the earlier rank-one module degree, these bounds exclude n < k < 2n
on the original automizer. No source-overgroup identification is assumed.
At k = 2n, E.2.14(7) gives actor rank 4n and torus fixed rank 3n. The
actual radical classification then selects the plane radical and proves
that its fixed space has rank 4n. Restricting the coefficient action to
that fixed space makes the torus a literal odd congruence. The determinant
form on its two-by-two corner then gives the H.4.4(4) contradiction.
The earlier E.2.14 clauses, selection, parabolic construction, ambient
torus argument and field-four endgame remain to be discharged.

Source: Aschbacher–Smith 8.2.2(7–8), 8.2.3 and H.4.4, printed
pp.715–716 and381 (1 March 2004 manuscript, refs/quasithin.pdf).
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
  {H T M V I : Subgroup G} [IsElementaryAbelian 2 V]
  {k : ℕ} {i : I} {S : Sylow 2 I}

/-- A selected pair cannot normalize its elementary generator. -/
theorem selected_not_normalizes (s : Selected H T M V I k i S) :
    ¬ I ≤ normalizer (V : Set G) := by
  intro hn
  have hVI : V ≤ I := s.generate ▸ le_sup_left
  let : (V.subgroupOf I).Normal := normal_subgroupOf_of_le_normalizer hn
  have hcore : V.subgroupOf I ≤ pCore 2 I :=
    le_sSup ⟨inferInstance, (IsElementaryAbelian.isPGroup 2 V).comap_subtype⟩
  have he : coreImage I V = ⊥ := by
    apply (Subgroup.map_eq_bot_iff _).mpr
    simpa only [QuotientGroup.ker_mk'] using hcore
  have hr := s.rank_eq
  rw [he, Representation.BinaryOffender.rank_bot] at hr
  have hk := s.positive
  omega

/-- The original central intersection witnesses the global r-bound. -/
theorem selected_globalR_le_rank_sum (s : Selected H T M V I k i S) :
    let A := V.map (MulAut.conj i.val⁻¹).toMonoidHom ⊓ (pCore 2 I).map I.subtype
    globalR V ≤ ((k + rank (inducedAutomizer V A) : ℕ) : ℕ∞) := by
  let W := V.map (MulAut.conj i.val⁻¹).toMonoidHom
  let Z := V ⊓ W
  have hIC : I ≤ centralizer (Z : Set G) := by
    intro a ha z hz
    obtain ⟨z',hz',he⟩ := s.intersection_central hz
    have hc := mem_center_iff.mp hz' (⟨a,ha⟩ : I)
    have hc' : a * I.subtype z' = I.subtype z' * a := congrArg I.subtype hc
    rw [he] at hc'
    exact hc'.symm
  have hr := globalR_le_corank (V := V) (U := Z) inf_le_left
    (fun hc => selected_not_normalizes s (hIC.trans hc))
  have he := selected_actor_rank_identity s
  have hz := offender_corank_add (W := V) (A := Z) bot_le inf_le_left
  have hz' : subgroupCorank V Z + rank Z = rank V := by
    simpa only [subgroupCorank,relIndex_bot_left,rank] using hz.symm
  have heq : subgroupCorank V Z = k +
      rank (inducedAutomizer V (W ⊓ (pCore 2 I).map I.subtype)) := by
    change rank Z + k + rank (inducedAutomizer V (W ⊓ (pCore 2 I).map I.subtype)) = rank V at he
    omega
  rwa [heq] at hr

private theorem overgroup_fixedCodim_of_rank_gt_two_mul (n : ℕ) [NeZero n]
    (M : Subgroup (Space n ≃ₗ[ZMod 2] Space n)) (hM : M ≤ binaryNormalizer n)
    (A : Subgroup M) [IsElementaryAbelian 2 A] (hr : 2*n < rank A) :
    5*n ≤ fixedCodim (overgroupAction n M) A := by
  let B := A.map M.subtype
  let : IsElementaryAbelian 2 B := IsElementaryAbelian.map M.subtype
  have hB : B ≤ binaryNormalizer n := (map_subtype_le A).trans hM
  have hBr : 2*n < rank B := by
    dsimp only [B]
    rwa [rank_map_injective M.subtype M.subtype_injective]
  have hd : Module.finrank (ZMod 2) (fixedSpace (UnipotentRadicals.ambientAction n) B) ≤ 4*n := by
    by_cases hb : B ≤ binaryImage n
    · exact LargeActors.inner_fixed_rank_le n B hb hBr
    · exact LargeActors.outer_fixed_rank_le n B hB hb (by have hn := NeZero.pos n; omega)
  have hc := fixedCodim_add_finrank (UnipotentRadicals.ambientAction n) B
  rw [finrank_binary] at hc
  have he := fixedCodim_map_equivariant (overgroupAction n M)
    (UnipotentRadicals.ambientAction n) M.subtype (LinearEquiv.refl (ZMod 2) (Space n))
    (fun _ _ => rfl) A
  change fixedCodim (overgroupAction n M) A =
    fixedCodim (UnipotentRadicals.ambientAction n) B at he
  omega

private theorem selected_actor_normalizes (s : Selected H T M V I k i S) :
    V.map (MulAut.conj i.val⁻¹).toMonoidHom ⊓ (pCore 2 I).map I.subtype ≤
      normalizer (V : Set G) := by
  have hcoreM : (pCore 2 I).map I.subtype ≤ M := by
    rintro _ ⟨a,ha,rfl⟩
    apply (M.subgroupOf I).normalCore_le
    change a ∈ localCore M I
    rwa [s.core_eq]
  exact inf_le_right.trans ((le_inf hcoreM (map_subtype_le _)).trans
    (s.normalizer_eq ▸ inf_le_right))

/-- The strict k-bound makes the selected actor large enough for the
Hermitian fixed-space estimate, before identifying it as a w-offender. -/
theorem selected_actor_fixedCodim_ge_five_mul
    (s : Selected H T M V I k i S) (n : ℕ) [NeZero n]
    (e : Additive V ≃ₗ[ZMod 2] Space n)
    (j : Automizer V →* binaryNormalizer n) (hj : Function.Injective j)
    (he : ∀ a v, e (automizerRepresentation V a v) =
      overgroupAction n (binaryNormalizer n) (j a) (e v))
    (hr : ((4*n : ℕ) : ℕ∞) ≤ globalR V) (hk : k < 2*n) :
    let A := V.map (MulAut.conj i.val⁻¹).toMonoidHom ⊓ (pCore 2 I).map I.subtype
    5*n ≤ fixedCodim (automizerRepresentation V) (inducedAutomizer V A) ∧
      5*n ≤ k + rank (inducedAutomizer V A) := by
  let W := V.map (MulAut.conj i.val⁻¹).toMonoidHom
  let A := W ⊓ (pCore 2 I).map I.subtype
  let Z := V ⊓ W
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.map _
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.of_le (show A ≤ W from inf_le_left)
  let : IsElementaryAbelian 2 (inducedAutomizer V A) :=
    inducedAutomizer_elementary V A (selected_actor_normalizes s)
  let : IsElementaryAbelian 2 ((inducedAutomizer V A).map j) := IsElementaryAbelian.map j
  have hsum : 4*n ≤ k + rank (inducedAutomizer V A) :=
    ENat.natCast_le_natCast.mp (hr.trans (selected_globalR_le_rank_sum s))
  have hlarge : 2*n < rank ((inducedAutomizer V A).map j) := by
    rw [rank_map_injective j hj]
    omega
  have hb := overgroup_fixedCodim_of_rank_gt_two_mul n (binaryNormalizer n) le_rfl
    ((inducedAutomizer V A).map j) hlarge
  rw [← fixedCodim_map_equivariant (automizerRepresentation V)
    (overgroupAction n (binaryNormalizer n)) j e he] at hb
  refine ⟨hb,?_⟩
  have hZA : Z ≤ V ⊓ centralizer (A : Set G) :=
    le_inf inf_le_left (inf_le_right.trans (W.le_centralizer.trans (centralizer_le inf_le_left)))
  have hc := offender_corank_add hZA (show V ⊓ centralizer (A : Set G) ≤ V from inf_le_left)
  have hz := offender_corank_add (W := V) (A := Z) bot_le inf_le_left
  have hi := selected_actor_rank_identity s
  rw [fixedCodim_inducedAutomizer V A (selected_actor_normalizes s)] at hb
  have hz' : subgroupCorank V Z + rank Z = rank V := by
    simpa only [subgroupCorank,relIndex_bot_left,rank] using hz.symm
  change rank Z + k + rank (inducedAutomizer V A) = rank V at hi
  change 5*n ≤ k + rank (inducedAutomizer V A)
  omega

private theorem fixedGroup_rank (X : Subgroup (Automizer V)) :
    rank (automizerFixedGroup V X) =
      Module.finrank (ZMod 2) (fixedSpace (automizerRepresentation V) X) := by
  rw [rank,automizerFixedGroup,card_map_of_injective V.subtype_injective]
  change Nat.log 2 (Nat.card (fixedSpace (automizerRepresentation V) X)) = _
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod,
    Nat.log_pow (by decide : 1 < 2)]

/-- The original selected actor and torus exclude the intermediate range.
Only the literal fixed-space, parabolic and rank-one degree inputs remain. -/
theorem selected_not_intermediate_of_torus
    (s : Selected H T M V I k i S) (n : ℕ) [NeZero n]
    (e : Additive V ≃ₗ[ZMod 2] Space n)
    (j : Automizer V →* binaryNormalizer n) (hj : Function.Injective j)
    (he : ∀ a v, e (automizerRepresentation V a v) =
      overgroupAction n (binaryNormalizer n) (j a) (e v))
    (hr : ((4*n : ℕ) : ℕ∞) ≤ globalR V)
    (x : Automizer V) (ho : orderOf x = 2^k-1)
    (hfixed : automizerFixedGroup V (zpowers x) =
      V ⊓ V.map (MulAut.conj i.val⁻¹).toMonoidHom)
    (hp : PreservesMaximalParabolic n (j x).val)
    (hd : k ∣ rank (inducedAutomizer V
      (V.map (MulAut.conj i.val⁻¹).toMonoidHom ⊓ (pCore 2 I).map I.subtype)) ∨ Odd k)
    (hnk : n < k) (hkn : k < 2*n) : False := by
  let A := V.map (MulAut.conj i.val⁻¹).toMonoidHom ⊓ (pCore 2 I).map I.subtype
  let W := V.map (MulAut.conj i.val⁻¹).toMonoidHom
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.map _
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.of_le (show A ≤ W from inf_le_left)
  let : IsElementaryAbelian 2 (inducedAutomizer V A) :=
    inducedAutomizer_elementary V A (selected_actor_normalizes s)
  have hrank : primeRank 2 (Automizer V) ≤ 4*n :=
    (primeRank_le_of_injective 2 j hj).trans
      (OuterRank.normalizer_twoRank_le n (normalizerCoverage n) ⟨FieldSections.centralizerEquiv n⟩)
  have hdim : rank V = 9*n := by
    rw [rank,show Nat.card V = Nat.card (Additive V) from rfl,
      Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod,
      e.finrank_eq,finrank_binary,Nat.log_pow Nat.one_lt_two]
  have hf := fixedGroup_rank (V := V) (zpowers x)
  rw [hfixed] at hf
  have hm : Module.finrank (ZMod 2)
      (fixedSpace (automizerRepresentation V) (zpowers x)) =
      Module.finrank (ZMod 2)
        (fixedSpace (overgroupAction n (binaryNormalizer n)) (zpowers (j x))) := by
    rw [← MonoidHom.map_zpowers,
      ← fixedSpace_map_equivariant (automizerRepresentation V)
        (overgroupAction n (binaryNormalizer n)) j e he,LinearEquiv.finrank_map_eq]
  have hlarge := selected_fixed_rank_gt_three_mul s n hdim hrank hkn x hfixed
  have hodd : Odd (orderOf x) := by
    rw [ho]
    exact Nat.Even.sub_odd (Nat.one_le_pow k 2 (by decide))
      (Nat.even_pow.mpr ⟨by decide,by omega⟩) odd_one
  have hoj : Odd (orderOf (j x)) := by rwa [orderOf_injective j hj]
  obtain ⟨hl,hdegree⟩ := largeOddFixedSpaceLinearity n (binaryNormalizer n) (j x)
    (j x).property hoj (hm ▸ hlarge)
  have hexd := oddLinearParabolicExponent n (j x).val (j x).property
    (by rwa [Subgroup.orderOf_coe]) hl hp
  rw [Subgroup.orderOf_coe,orderOf_injective j hj,ho] at hexd
  have hkdiv := (Offenders.pow_sub_one_dvd_pow_sub_one_iff_dvd (by omega : 0 < k)).mp hexd
  rw [← hm,← hf] at hdegree
  have hid := selected_actor_rank_identity s
  rw [hdim] at hid
  have hsum : n ∣ rank (V ⊓ W) + (k + rank (inducedAutomizer V A)) := by
    rw [← Nat.add_assoc]
    exact hid ▸ dvd_mul_left n 9
  have hfixeddiv : n ∣ k + rank (inducedAutomizer V A) :=
    (Nat.dvd_add_iff_right hdegree).mpr hsum
  have hupper := (offender_rank_le_primeRank (inducedAutomizer V A)).trans hrank
  exact Nat.BinaryParabolicRank.false_of_intermediate_parameters hnk hkn hkdiv hupper
    (selected_actor_fixedCodim_ge_five_mul s n e j hj he hr hkn).2 hd hfixeddiv

/-- The torus fixed space lies in the selected actor fixed space because
the source intersection lies in its elementary conjugate. -/
theorem selected_fixedSpace_le_actor
    (s : Selected H T M V I k i S) (x : Automizer V)
    (hfixed : automizerFixedGroup V (zpowers x) =
      V ⊓ V.map (MulAut.conj i.val⁻¹).toMonoidHom) :
    fixedSpace (automizerRepresentation V) (zpowers x) ≤
      fixedSpace (automizerRepresentation V) (inducedAutomizer V
        (V.map (MulAut.conj i.val⁻¹).toMonoidHom ⊓ (pCore 2 I).map I.subtype)) := by
  let W := V.map (MulAut.conj i.val⁻¹).toMonoidHom
  let A := W ⊓ (pCore 2 I).map I.subtype
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.map _
  intro v hv
  apply (mem_fixedSpace_inducedAutomizer V A (selected_actor_normalizes s) v).mpr
  have hvG : v.toMul.val ∈ automizerFixedGroup V (zpowers x) := ⟨v.toMul,hv,rfl⟩
  rw [hfixed] at hvG
  exact (centralizer_le (show A ≤ W from inf_le_left)) (W.le_centralizer hvG.2)

/-- At the endpoint, the actual actor is the plane radical: the point
radical cannot contain the torus fixed space of rank 3n. E.2.14(7) is
retained explicitly, and the source H.4.4(4) contradiction is still required. -/
theorem selected_endpoint_plane
    (K : GroupClass) (e14 : E214RankClause (G := G) K)
    (h28 : HypothesisE28 K H T M V) (hchar : HasCharacteristicTwo H)
    (hTI : LocalTI H M V) (s : Selected H T M V I k i S)
    (n : ℕ) [NeZero n] (hkn : k = 2*n)
    (e : Additive V ≃ₗ[ZMod 2] Space n)
    (j : Automizer V →* binaryNormalizer n) (hj : Function.Injective j)
    (he : ∀ a v, e (automizerRepresentation V a v) =
      overgroupAction n (binaryNormalizer n) (j a) (e v))
    (x : Automizer V)
    (hfixed : automizerFixedGroup V (zpowers x) =
      V ⊓ V.map (MulAut.conj i.val⁻¹).toMonoidHom) :
    let A := V.map (MulAut.conj i.val⁻¹).toMonoidHom ⊓ (pCore 2 I).map I.subtype
    rank (inducedAutomizer V A) = 4*n ∧
      Module.finrank (ZMod 2) (fixedSpace (automizerRepresentation V) (zpowers x)) = 3*n ∧
      Module.finrank (ZMod 2) (fixedSpace (automizerRepresentation V) (inducedAutomizer V A)) = 4*n ∧
      ∃ c : Cover n, ((inducedAutomizer V A).map ((binaryNormalizer n).subtype.comp j)).map
        (MulAut.conj (binaryActionHom n c)).toMonoidHom = UnipotentRadicals.plane n := by
  let W := V.map (MulAut.conj i.val⁻¹).toMonoidHom
  let A := W ⊓ (pCore 2 I).map I.subtype
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.map _
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.of_le (show A ≤ W from inf_le_left)
  let : IsElementaryAbelian 2 (inducedAutomizer V A) :=
    inducedAutomizer_elementary V A (selected_actor_normalizes s)
  have hrank : primeRank 2 (Automizer V) ≤ 4*n :=
    (primeRank_le_of_injective 2 j hj).trans
      (OuterRank.normalizer_twoRank_le n (normalizerCoverage n) ⟨FieldSections.centralizerEquiv n⟩)
  have hupper := (offender_rank_le_primeRank (inducedAutomizer V A)).trans hrank
  have ha : rank (inducedAutomizer V A) = 4*n := by
    have hh := e14 H T M V I k h28 s.family hchar hTI i s.generate
      s.intersection_ne_bot s.quadraticRatio_gt_one (by simpa only [hkn, ← Nat.mul_assoc, show 2*2=4 from rfl] using hupper)
    simpa only [hkn, ← Nat.mul_assoc, show 2*2=4 from rfl] using hh
  have hdim : rank V = 9*n := by
    rw [rank,show Nat.card V = Nat.card (Additive V) from rfl,
      Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod,
      e.finrank_eq,finrank_binary,Nat.log_pow Nat.one_lt_two]
  have hz := fixedGroup_rank (V := V) (zpowers x)
  rw [hfixed] at hz
  have hid := selected_actor_rank_identity s
  change rank (V ⊓ W) + k + rank (inducedAutomizer V A) = rank V at hid
  rw [hdim,ha,hkn] at hid
  have hx : Module.finrank (ZMod 2) (fixedSpace (automizerRepresentation V) (zpowers x)) = 3*n := by
    change rank (V ⊓ W) = _ at hz
    omega
  let f := (binaryNormalizer n).subtype.comp j
  have hfi : Function.Injective f := (binaryNormalizer n).subtype_injective.comp hj
  let B := (inducedAutomizer V A).map f
  let : IsElementaryAbelian 2 B := IsElementaryAbelian.map f
  have hB : B ≤ binaryNormalizer n := by
    rintro _ ⟨a,ha,rfl⟩
    exact (j a).property
  have hBr : rank B = 4*n := (rank_map_injective f hfi _).trans ha
  have hBL : B ≤ binaryImage n :=
    Chapter7.NormalizedSource.NonMathieuHermitian.large_elementary_le_image n B hB
      (by rw [hBr]; have hn := NeZero.pos n; omega)
  have hm : Module.finrank (ZMod 2) (fixedSpace (automizerRepresentation V) (inducedAutomizer V A)) =
      Module.finrank (ZMod 2) (fixedSpace (UnipotentRadicals.ambientAction n) B) := by
    rw [← fixedSpace_map_equivariant (automizerRepresentation V)
      (UnipotentRadicals.ambientAction n) f e he,LinearEquiv.finrank_map_eq]
  have hl := Submodule.finrank_mono (selected_fixedSpace_le_actor s x hfixed)
  rw [hx,hm] at hl
  obtain ⟨c,hc | hc⟩ := UnipotentRadicals.maximal_elementary_conjugate n B hBL hBr
  · have hd := (fixedSpaceConjEquiv (UnipotentRadicals.ambientAction n) B
        (binaryActionHom n c)).finrank_eq
    rw [hc,UnipotentRadicals.finrank_point_fixed] at hd
    have hn := NeZero.pos n
    omega
  · have hd := (fixedSpaceConjEquiv (UnipotentRadicals.ambientAction n) B
        (binaryActionHom n c)).finrank_eq
    rw [hc,UnipotentRadicals.finrank_plane_fixed] at hd
    exact ⟨ha,hx,hm.trans hd,c,hc⟩

/-- The endpoint torus is a literal odd GL₃ congruence on the original
coordinates. Its fixed rank 3n is large inside the actor fixed space of
rank 4n, so no coefficient action survives. -/
theorem selected_endpoint_congruence
    (K : GroupClass) (e14 : E214RankClause (G := G) K)
    (h28 : HypothesisE28 K H T M V) (hchar : HasCharacteristicTwo H)
    (hTI : LocalTI H M V) (s : Selected H T M V I k i S)
    (n : ℕ) [NeZero n] (hkn : k = 2*n)
    (e : Additive V ≃ₗ[ZMod 2] Space n)
    (j : Automizer V →* binaryNormalizer n) (hj : Function.Injective j)
    (he : ∀ a v, e (automizerRepresentation V a v) =
      overgroupAction n (binaryNormalizer n) (j a) (e v))
    (x : Automizer V) (ho : orderOf x = 2^k-1)
    (hx : x ∈ inducedAutomizer V (M ⊓ I))
    (hfixed : automizerFixedGroup V (zpowers x) =
      V ⊓ V.map (MulAut.conj i.val⁻¹).toMonoidHom) :
    IsFixedFieldLinear n (j x).val ∧
      ∃ g : Matrix.GeneralLinearGroup (Fin 3) (E n),
        binaryCongruence n g = (j x).val ∧ Odd (orderOf g) := by
  let A := V.map (MulAut.conj i.val⁻¹).toMonoidHom ⊓ (pCore 2 I).map I.subtype
  let f := (binaryNormalizer n).subtype.comp j
  have hfi : Function.Injective f := (binaryNormalizer n).subtype_injective.comp hj
  let B := (inducedAutomizer V A).map f
  let W := V.map (MulAut.conj i.val⁻¹).toMonoidHom
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.map _
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.of_le (show A ≤ W from inf_le_left)
  let : IsElementaryAbelian 2 (inducedAutomizer V A) :=
    inducedAutomizer_elementary V A (selected_actor_normalizes s)
  let : IsElementaryAbelian 2 B := IsElementaryAbelian.map f
  obtain ⟨ha,hxf,haf,_⟩ := selected_endpoint_plane K e14 h28 hchar hTI s n hkn e j hj he x hfixed
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
  have hBA : Module.finrank (ZMod 2) (fixedSpace (UnipotentRadicals.ambientAction n) B) = 4*n := by
    rw [← hmap,LinearEquiv.finrank_map_eq]
    exact haf
  have hX : (zpowers x).map f = zpowers (j x).val := MonoidHom.map_zpowers f x
  have hBX : Module.finrank (ZMod 2)
      (fixedSpace (UnipotentRadicals.ambientAction n) (zpowers (j x).val)) = 3*n := by
    rw [←hX,←hmap,LinearEquiv.finrank_map_eq]
    exact hxf
  have hle : fixedSpace (UnipotentRadicals.ambientAction n) (zpowers (j x).val) ≤
      fixedSpace (UnipotentRadicals.ambientAction n) B := by
    rw [←hX,←hmap,←hmap]
    exact Submodule.map_mono (selected_fixedSpace_le_actor s x hfixed)
  have hnorm : (j x).val ∈ normalizer (B : Set (BinaryAut n)) :=
    (inducedAutomizer V A).le_normalizer_map f
      (mem_map_of_mem f (selected_normalizes_actor s hx))
  have hodd : Odd (orderOf (j x).val) := by
    rw [Subgroup.orderOf_coe,orderOf_injective j hj,ho]
    exact Nat.Even.sub_odd (Nat.one_le_pow k 2 (by decide))
      (Nat.even_pow.mpr ⟨by decide,by have hn := NeZero.pos n; omega⟩) odd_one
  have hlin := linear_of_large_fixed_inside_actor n B hBL hBA (j x).val
    (j x).property hodd hnorm hle (by rw [hBX]; have hn := NeZero.pos n; omega)
  obtain ⟨g,hg⟩ := OddExponent.mem_congruenceImage_of_odd_of_isFixedFieldLinear n
    (j x).val (j x).property hodd hlin
  exact ⟨hlin,g,hg,OddExponent.odd_orderOf_of_odd_binaryCongruence n g (hg.symm ▸ hodd)⟩

/-- E.2.14(7) and the actual selected torus contradict the Hermitian plane
calculation at k = 2n. The coefficient and congruence inputs are proved on
the original automizer; half-degree one is included. -/
theorem selected_not_endpoint_of_torus
    (K : GroupClass) (e14 : E214RankClause (G := G) K)
    (h28 : HypothesisE28 K H T M V) (hchar : HasCharacteristicTwo H)
    (hTI : LocalTI H M V) (s : Selected H T M V I k i S)
    (n : ℕ) [NeZero n] (hkn : k = 2*n)
    (e : Additive V ≃ₗ[ZMod 2] Space n)
    (j : Automizer V →* binaryNormalizer n) (hj : Function.Injective j)
    (he : ∀ a v, e (automizerRepresentation V a v) =
      overgroupAction n (binaryNormalizer n) (j a) (e v))
    (x : Automizer V) (ho : orderOf x = 2^k-1)
    (hx : x ∈ inducedAutomizer V (M ⊓ I))
    (hfixed : automizerFixedGroup V (zpowers x) =
      V ⊓ V.map (MulAut.conj i.val⁻¹).toMonoidHom) : False := by
  let A := V.map (MulAut.conj i.val⁻¹).toMonoidHom ⊓ (pCore 2 I).map I.subtype
  let f := (binaryNormalizer n).subtype.comp j
  let B := (inducedAutomizer V A).map f
  obtain ⟨_,hxf,_,c,hc⟩ := selected_endpoint_plane K e14 h28 hchar hTI s n hkn e j hj he x hfixed
  obtain ⟨_,g,hg,hgo⟩ := selected_endpoint_congruence K e14 h28 hchar hTI s n hkn e j hj he x ho hx hfixed
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
  have hnorm : (j x).val ∈ normalizer (B : Set (BinaryAut n)) :=
    (inducedAutomizer V A).le_normalizer_map f
      (mem_map_of_mem f (selected_normalizes_actor s hx))
  exact conjugate_plane_no_fixed_rank_three_mul n B c hc g hgo
    (hg.symm ▸ hnorm) (hg.symm ▸ hle) (hg.symm ▸ hBX)

end CFSG.Quasithin.Chapter8.Section02.HermitianSource
