module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicPlaneRadiusCoreFixed
public import Theory.Representation.BinaryConjugationSection.Ambient
public import Theory.Representation.BinaryConjugationSection.FixedIndex

/-!
# Original cubic reciprocal spans and factorization comparison

The reciprocal calculation takes place in the original source graph. Its
actors retain the full local quotient and the actual cubic projection
kernel; only intersections of two-subgroups discard its odd quotient.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.NaturalStructure.Exclusion
open Stellmacher.PushingUp.AmalgamGraph
open scoped commutatorElement IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicFull
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  {h : SmallMSPair KnownSimple.IsKnownSimple L R}
local notation "T" => edge L R

include h in
theorem cubic_reciprocal_span_core_eq_seed_of_radius_fixed
    (hb : 2 < sourceDistance h) {a c : Vertex T}
    (ha : color T a = false) (hc : color T c = false)
    (hd : (cosetGraph T).dist a c = 2)
    (hfixed : ⁅V T a,Q T a⁆ ≤ fixedCore T a) :
    ⁅localZSpan T c a,Q T a⁆ = ⁅Z T c,Q T a⁆ ∧
      ⁅localZSpan T c a,Q T a⁆ ≤ Z T c := by
  let D := ⁅Z T c,Q T a⁆
  have hZV : Z T c ≤ V T a := le_iSup_of_le c
    (le_iSup_of_le (show (cosetGraph T).dist c a ≤ 2 by
      rw [SimpleGraph.dist_comm,hd]) le_rfl)
  have hDfixed : D ≤ fixedCore T a := (commutator_mono hZV le_rfl).trans hfixed
  have hQa : Q T a ≤ stabilizer T c :=
    Q_le_stabilizer_of_dist_le_two a c ha hc hd.le
  have hDZ : D ≤ Z T c :=
    le_normalizer_iff_commutator_le_left.mp (hQa.trans (Z_normalized T c))
  obtain ⟨t,hat,hct⟩ := exists_common_neighbor_of_dist_two T a c hd
  have hTa : Q T t ≤ stabilizer T a :=
    fun _ hx => hx.2 _ (adjacent_symm T hat)
  have hTc : Q T t ≤ stabilizer T c :=
    fun _ hx => hx.2 _ (adjacent_symm T hct)
  have hTN : Q T t ≤ normalizer (D : Set (FreeAmalgam T)) := by
    intro x hx
    apply mem_normalizer_iff_map_conj_eq.mpr
    change (⁅Z T c,Q T a⁆).map (MulAut.conj x).toMonoidHom = _
    have hz : (Z T c).map (MulAut.conj x).toMonoidHom = Z T c :=
      mem_normalizer_iff_map_conj_eq.mp (Z_normalized T c (hTc hx))
    have hq : (Q T a).map (MulAut.conj x).toMonoidHom = Q T a :=
      mem_normalizer_iff_map_conj_eq.mp (Q_normalized T a (hTa hx))
    rw [map_commutator,hz,hq]
  have hLN : Ltilde T a ≤ normalizer (D : Set (FreeAmalgam T)) :=
    (le_centralizer_iff.mp (hDfixed.trans inf_le_right)).trans
      (Subgroup.centralizer_le_normalizer _)
  have hGN : stabilizer T a ≤ normalizer (D : Set (FreeAmalgam T)) := by
    rw [←residual_edge_generation h ha hat]
    exact sup_le hLN hTN
  have heq : ⁅localZSpan T c a,Q T a⁆ = D := by
    rw [LocalCommutator.span_commutator_eq_conjugates (geometry := sourceGeometry h)
      ha (by rw [SimpleGraph.dist_comm,hd]) hb]
    apply le_antisymm
    · apply iSup_le
      intro g
      change D.map (MulAut.conj (g : FreeAmalgam T)⁻¹).toMonoidHom ≤ D
      exact (mem_normalizer_iff_map_conj_eq.mp
        (hGN ((stabilizer T a).inv_mem g.property))).le
    · exact (commutator_mono (Z_le_localZSpan T c a) le_rfl).trans_eq
        (LocalCommutator.span_commutator_eq_conjugates
          (geometry := sourceGeometry h) ha
          (by rw [SimpleGraph.dist_comm,hd]) hb)
  exact ⟨heq,heq.le.trans hDZ⟩

include h in
theorem cubic_reciprocal_span_intersection_commutators_of_radius_fixed
    (hb : 2 < sourceDistance h) {a c : Vertex T}
    (ha : color T a = false) (hc : color T c = false)
    (hd : (cosetGraph T).dist a c = 2)
    (hfixedA : ⁅V T a,Q T a⁆ ≤ fixedCore T a)
    (hfixedC : ⁅V T c,Q T c⁆ ≤ fixedCore T c) :
    ⁅localZSpan T c a ⊓ Q T c,localZSpan T a c⁆ ≤ Z T a ∧
      ⁅localZSpan T a c ⊓ Q T a,localZSpan T c a⁆ ≤ Z T c := by
  have hA := cubic_reciprocal_span_core_eq_seed_of_radius_fixed (h := h) hb ha hc hd hfixedA
  have hC := cubic_reciprocal_span_core_eq_seed_of_radius_fixed (h := h) hb hc ha
    (by rwa [SimpleGraph.dist_comm]) hfixedC
  constructor
  · rw [commutator_comm]
    exact (commutator_mono le_rfl inf_le_right).trans hC.2
  · rw [commutator_comm]
    exact (commutator_mono le_rfl inf_le_right).trans hA.2

include h in
private theorem cubic_reciprocal_span_sq_mem_derived
    (_hb : 2 < sourceDistance h) {a c : Vertex T}
    (ha : color T a = false) (x : localZSpan T a c) :
    (x : FreeAmalgam T)^2 ∈ ⁅localZSpan T a c,localZSpan T a c⁆ := by
  let P := localZSpan T a c
  let D := _root_.commutator P
  let q := QuotientGroup.mk' D
  let : IsMulCommutative (P ⧸ D) := Normal.quotient_commutative_iff_commutator_le.mpr le_rfl
  let K := ((powMonoidHom 2).comp q).ker
  have hPK : P ≤ K.map P.subtype := by
    apply iSup_le
    intro g z hz
    have hzP : z ∈ P := (le_iSup (fun k : stabilizer T c =>
      Z T (act T k a)) g) hz
    let zP : P := ⟨z,hzP⟩
    refine ⟨zP,?_,rfl⟩
    change q zP ^ 2 = 1
    rw [←map_pow]
    have hp : zP^2 = 1 := by
      apply Subtype.ext
      let := (sourceGeometry h).Z_elementary (sourceDistance_pos h)
        (act T g a) ((action_preserves_color T g a).trans ha)
      exact elemPow_eq_one_of_isElementaryAbelian z hz
    rw [hp,map_one]
  obtain ⟨y,hy,hyx⟩ := hPK x.property
  have he : y = x := Subtype.ext hyx
  subst y
  have hx : q x^2 = 1 := hy
  have hxD : x^2 ∈ D := (QuotientGroup.eq_one_iff _).mp (by
    change q (x^2) = 1
    rw [map_pow]
    exact hx)
  rw [←map_subtype_commutator]
  exact mem_map_of_mem P.subtype hxD

theorem cubic_reciprocal_actor_kernel_normal
    (hb : 2 < sourceDistance h) {a c : Vertex T}
    (ha : color T a = false) (hc : color T c = false)
    (hd : (cosetGraph T).dist a c = 2) :
    ((Q T a).subgroupOf (localZSpan T a c)).Normal :=
  normal_subgroupOf_of_le_normalizer
    ((localZSpan_le_Q T hc hd.le hb).trans
      ((Q_le_stabilizer_of_dist_le_two c a hc ha (by rw [SimpleGraph.dist_comm,hd])).trans
        (Q_normalized T a)))

include h in
theorem cubic_reciprocal_actor_quotient_elementary_of_radius_fixed
    (hb : 2 < sourceDistance h) {a c : Vertex T}
    (ha : color T a = false) (hc : color T c = false)
    (hd : (cosetGraph T).dist a c = 2)
    (hfixedC : ⁅V T c,Q T c⁆ ≤ fixedCore T c) :
    letI := cubic_reciprocal_actor_kernel_normal (h := h) hb ha hc hd
    IsElementaryAbelian 2 ((localZSpan T a c) ⧸
      (Q T a).subgroupOf (localZSpan T a c)) := by
  let := cubic_reciprocal_actor_kernel_normal (h := h) hb ha hc hd
  let P := localZSpan T a c
  let N := (Q T a).subgroupOf P
  have hbound : ⁅P,P⁆ ≤ Q T a :=
    ((commutator_mono le_rfl (localZSpan_le_Q T hc hd.le hb)).trans
      (cubic_reciprocal_span_core_eq_seed_of_radius_fixed (h := h) hb hc ha
        (by rwa [SimpleGraph.dist_comm]) hfixedC).2).trans
      ((Z_le_VBall T a 2).trans (V_le_Q T (geometry := sourceGeometry h) ha hb))
  have hp (x : P ⧸ N) : x^2 = 1 := by
    obtain ⟨x,rfl⟩ := QuotientGroup.mk'_surjective N x
    rw [←map_pow]
    exact (QuotientGroup.eq_one_iff _).mpr
      (hbound (cubic_reciprocal_span_sq_mem_derived (h := h) hb ha x))
  let : IsMulCommutative (P ⧸ N) :=
    ⟨⟨fun x y => (Commute.of_orderOf_dvd_two
      (fun v => orderOf_dvd_of_pow_eq_one (hp v)) x y).eq⟩⟩
  exact ⟨Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr hp⟩

/-- The reciprocal span has its literal elementary image in the local
quotient; its order is the opposite-core relative index. -/
theorem cubic_reciprocal_actor_image_data_of_radius_fixed
    (hb : 2 < sourceDistance h) {a c : Vertex T}
    (ha : color T a = false) (hc : color T c = false)
    (hd : (cosetGraph T).dist a c = 2)
    (hfixedC : ⁅V T c,Q T c⁆ ≤ fixedCore T c) :
    letI := Q_normal T a
    let A := ((localZSpan T a c).subgroupOf (stabilizer T a)).map
      (QuotientGroup.mk' ((Q T a).subgroupOf (stabilizer T a)))
    IsElementaryAbelian 2 A ∧ Nat.card A = (Q T a).relIndex (localZSpan T a c) ∧
      (A = ⊥ ↔ localZSpan T a c ≤ Q T a) := by
  let := Q_normal T a
  let := cubic_reciprocal_actor_kernel_normal (h := h) hb ha hc hd
  let := cubic_reciprocal_actor_quotient_elementary_of_radius_fixed (h := h) hb ha hc hd hfixedC
  let H := stabilizer T a
  let P := localZSpan T a c
  let N := (Q T a).subgroupOf P
  let π := QuotientGroup.mk' ((Q T a).subgroupOf H)
  let A := (P.subgroupOf H).map π
  have hPH : P ≤ H := (localZSpan_le_Q T hc hd.le hb).trans
    (Q_le_stabilizer_of_dist_le_two c a hc ha (by rw [SimpleGraph.dist_comm,hd]))
  let f : P →* A := {
    toFun x := ⟨π ⟨x,hPH x.property⟩,⟨⟨x,hPH x.property⟩,x.property,rfl⟩⟩
    map_one' := by apply Subtype.ext; exact map_one π
    map_mul' x y := by
      apply Subtype.ext
      exact map_mul π (⟨x,hPH x.property⟩ : H) (⟨y,hPH y.property⟩ : H) }
  have hf : Function.Surjective f := by
    rintro ⟨y,x,hx,rfl⟩
    exact ⟨⟨x,hx⟩,rfl⟩
  have hk : f.ker = N := by
    ext x
    change f x = 1 ↔ (x : FreeAmalgam T) ∈ Q T a
    rw [Subtype.ext_iff]
    exact QuotientGroup.eq_one_iff (⟨x,hPH x.property⟩ : H)
  have hEA : IsElementaryAbelian 2 A := by
    let fbar : P ⧸ N →* A := QuotientGroup.lift N f hk.ge
    exact IsElementaryAbelian.of_surjective fbar
      (QuotientGroup.lift_surjective_of_surjective N f hf hk.ge)
  have hcard : Nat.card A = (Q T a).relIndex P := by
    have he := (Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective f hf).toEquiv).symm
    rw [hk] at he
    exact he
  refine ⟨hEA,hcard,?_⟩
  constructor
  · intro he x hx
    have hxA : π ⟨x,hPH hx⟩ ∈ A := ⟨⟨x,hPH hx⟩,hx,rfl⟩
    have hxone : π ⟨x,hPH hx⟩ = 1 := by
      change A = ⊥ at he
      rw [he] at hxA
      exact hxA
    exact (QuotientGroup.eq_one_iff (⟨x,hPH hx⟩ : H)).mp hxone
  · intro hPQ
    apply bot_unique
    rintro y ⟨x,hx,rfl⟩
    exact (QuotientGroup.eq_one_iff x).mpr (hPQ hx)

/-- A nonabelian orbit span cannot lie in its seed vertex core: otherwise
all its generating conjugates centralize the whole span. -/
theorem cubic_reciprocal_nonabelian_span_not_le_seed_core
    {a c : Vertex T} (hc : color T c = false)
    (hnon : ⁅localZSpan T c a,localZSpan T c a⁆ ≠ ⊥) :
    ¬ localZSpan T c a ≤ Q T c := by
  intro hPQ
  let P := localZSpan T c a
  have hZC : Z T c ≤ centralizer (P : Set (FreeAmalgam T)) :=
    (commutator_eq_bot_iff_le_centralizer.mp (Z_centralizes_Q T c hc)).trans
      (centralizer_le hPQ)
  have hnC : stabilizer T a ≤
      normalizer (centralizer (P : Set (FreeAmalgam T)) : Set (FreeAmalgam T)) :=
    (localZSpan_normalized T c a).trans (normalizer_le_normalizer_centralizer P)
  apply hnon
  apply commutator_eq_bot_iff_le_centralizer.mpr
  conv_lhs => rw [localZSpan_eq_conjugates]
  apply iSup_le
  intro g
  exact (map_mono hZC).trans_eq (mem_normalizer_iff_map_conj_eq.mp
    (hnC ((stabilizer T a).inv_mem g.property)))

private theorem fixedSpace_subgroup_index {G D : Type*} [Group G] [Group D]
    [IsElementaryAbelian 2 D] [Finite D] (action : G →* MulAut D) (A : Subgroup G) :
    (Subgroup.toAddSubgroup.symm
      (fixedSpace (Offenders.linearize action) A).toAddSubgroup).index =
      2 ^ fixedCodim (Offenders.linearize action) A := by
  let ρ := Offenders.linearize action
  let C := Subgroup.toAddSubgroup.symm (fixedSpace ρ A).toAddSubgroup
  let e : fixedSpace ρ A ≃ C := {
    toFun := fun v => ⟨v.val.toMul, v.property⟩
    invFun := fun x => ⟨Additive.ofMul x.val, x.property⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  have hC : Nat.card C = 2 ^ Module.finrank (ZMod 2) (fixedSpace ρ A) := by
    have hf := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := fixedSpace ρ A)
    rw [Nat.card_zmod] at hf
    exact (Nat.card_congr e).symm.trans hf
  have hT : Nat.card D = 2 ^ Module.finrank (ZMod 2) (Additive D) :=
    (Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive D)).trans (by rw [Nat.card_zmod])
  have hdim := fixedCodim_add_finrank ρ A
  have hmul := C.card_mul_index
  rw [hC, hT, ← hdim, pow_add, Nat.mul_comm (2 ^ fixedCodim ρ A)] at hmul
  exact Nat.eq_of_mul_eq_mul_left (by positivity) hmul

private theorem reciprocal_modulo_index_le_of_cover
    {F : Type*} [Group F] [Finite F] (M P A B K : Subgroup F) [B.Normal]
    (hMP : M ≤ P ⊔ B) (hcomm : ⁅P ⊓ K,A⁆ ≤ B) :
    (centralizerModulo M A B).relIndex M ≤ K.relIndex P := by
  let π := QuotientGroup.mk' B
  have hB : B.map π = ⊥ := (Subgroup.map_eq_bot_iff _).mpr (by
    rw [QuotientGroup.ker_mk'])
  have hm : M.map π ≤ P.map π := by
    have hh := map_mono (f := π) hMP
    rwa [Subgroup.map_sup,hB,sup_bot_eq] at hh
  rw [NoncentralChiefRefinement.SymmetricSixBudget.centralizerModulo_relIndex_eq]
  exact (relIndex_le_of_le_right hm
    ((centralizer (A.map π : Set (F ⧸ B))).subgroupOf (P.map π)).index_ne_zero_of_finite).trans
      (by rw [←NoncentralChiefRefinement.SymmetricSixBudget.centralizerModulo_relIndex_eq]
          exact NoncentralChiefRefinement.SymmetricSixBudget.centralizerModulo_relIndex_le_of_commutator
            P A B K hcomm)


/-- Fixedness of the original radius-core commutator gives the elementary
structure on the literal central quotient of the moving radius. -/
theorem cubic_reciprocal_moving_quotient_elementary
    (hb : 2 < sourceDistance h) {a : Vertex T} (ha : color T a = false)
    (hfixed : ⁅V T a,Q T a⁆ ≤ fixedCore T a) :
    IsElementaryAbelian 2 ((Vcirc T a) ⧸ center (Vcirc T a)) :=
  moving_central_quotient_elementary (sourceGeometry h) (sourceDistance_pos h) a ha
    ((commutator_mono le_rfl ((sourceGeometry h).V_le_Q hb a ha)).trans hfixed)

/-- The reciprocal source span bounds the fixed index on the moving central
quotient. The only discarded displacements lie in the actual seed Z(a),
which centralizes the entire moving radius. -/
theorem cubic_reciprocal_central_fixed_index_le
    (hb : 2 < sourceDistance h) {a c : Vertex T}
    (ha : color T a = false) (hc : color T c = false)
    (hd : (cosetGraph T).dist a c = 2)
    (hfixedA : ⁅V T a,Q T a⁆ ≤ fixedCore T a)
    (hfixedC : ⁅V T c,Q T c⁆ ≤ fixedCore T c)
    (hspan : Vcirc T a ≤ localZSpan T c a ⊔ Z T a) :
    letI := cubic_reciprocal_moving_quotient_elementary hb ha hfixedA
    2 ^ fixedCodim (Offenders.linearize (movingQuotientAction a))
      ((localZSpan T a c).subgroupOf (stabilizer T a)) ≤
        (Q T c).relIndex (localZSpan T c a) := by
  let := cubic_reciprocal_moving_quotient_elementary hb ha hfixedA
  let := finite_moving (sourceGeometry h) hb a ha
  let S := stabilizer T a
  let M := Vcirc T a
  let P := localZSpan T c a
  let A := localZSpan T a c
  let Z₀ := Z T a
  have hMV : M ≤ V T a := le_normalizer_iff_commutator_le_left.mp
    ((Ltilde_le_stabilizer a).trans (V_normalized a))
  have hVQ := (sourceGeometry h).V_le_Q hb a ha
  have hVS : V T a ≤ S := hVQ.trans (fun _ hx => hx.1)
  have hMS : M ≤ S := hMV.trans hVS
  have hPS : P ≤ S := (localZSpan_le_V T (by rw [SimpleGraph.dist_comm,hd])).trans hVS
  have hZS : Z₀ ≤ S := Z_le_stabilizer T a
  let : Finite S := finite_stabilizer T a
  let : (Z₀.subgroupOf S).Normal := normal_subgroupOf_of_le_normalizer (Z_normalized T a)
  let D := centralizerModulo (M.subgroupOf S) (A.subgroupOf S) (Z₀.subgroupOf S)
  have hcover : M.subgroupOf S ≤ P.subgroupOf S ⊔ Z₀.subgroupOf S := by
    rw [←subgroupOf_sup hPS hZS]
    exact comap_mono hspan
  have hcross : ⁅P ⊓ Q T c,A⁆ ≤ Z₀ := by
    rw [commutator_comm]
    exact (commutator_mono le_rfl inf_le_right).trans
      (cubic_reciprocal_span_core_eq_seed_of_radius_fixed hb hc ha
        (by rwa [SimpleGraph.dist_comm]) hfixedC).2
  have hcross₀ : ⁅P.subgroupOf S ⊓ (Q T c).subgroupOf S,A.subgroupOf S⁆ ≤
      Z₀.subgroupOf S := by
    apply commutator_le.mpr
    intro x hx y hy
    exact hcross (commutator_mem_commutator ⟨hx.1,hx.2⟩ hy)
  have hi := reciprocal_modulo_index_le_of_cover (M.subgroupOf S) (P.subgroupOf S)
    (A.subgroupOf S) (Z₀.subgroupOf S) ((Q T c).subgroupOf S) hcover hcross₀
  rw [relIndex_subgroupOf hPS] at hi
  let q := QuotientGroup.mk' (center M)
  let ρ := Offenders.linearize (movingQuotientAction a)
  let C := Subgroup.toAddSubgroup.symm (fixedSpace ρ (A.subgroupOf S)).toAddSubgroup
  let f := inclusion hMS
  have hZC : Z₀ ≤ centralizer (M : Set (FreeAmalgam T)) :=
    (commutator_eq_bot_iff_le_centralizer.mp (Z_centralizes_Q T a ha)).trans
      (centralizer_le (hMV.trans hVQ))
  have hDC : D.comap f ≤ C.comap q := by
    intro p hp e
    let d : M := movingAction a e.val p * p⁻¹
    have hdZ : (d : FreeAmalgam T) ∈ Z₀ :=
      (mem_centralizerModulo_iff.mp hp).2 e.val e.property
    have hdC : d ∈ center M := by
      apply mem_center_iff.mpr
      intro v
      apply Subtype.ext
      exact hZC hdZ v v.property
    change Additive.ofMul (movingQuotientAction a e.val (q p)) = Additive.ofMul (q p)
    apply congrArg Additive.ofMul
    rw [movingQuotientAction_apply]
    apply QuotientGroup.eq_iff_div_mem.mpr
    simpa only [div_eq_mul_inv] using hdC
  have hindex : C.index ≤ (D.comap f).index := by
    rw [←C.index_comap_of_surjective (QuotientGroup.mk'_surjective (center M))]
    exact Nat.le_of_dvd (Nat.pos_of_ne_zero (D.comap f).index_ne_zero_of_finite)
      (index_dvd_of_le hDC)
  rw [fixedSpace_subgroup_index,D.index_comap,inclusion_range] at hindex
  exact hindex.trans hi

private theorem two_inf_odd_extension_eq
    {F : Type*} [Group F] [Finite F] (A Q E : Subgroup F) [Q.Normal]
    (hA : IsPGroup 2 A) (hQE : Q ≤ E) (hodd : Odd (Q.relIndex E)) :
    A ⊓ E = A ⊓ Q := by
  let q := QuotientGroup.mk' Q
  have hcard : Nat.card (E.map q) = Q.relIndex E := by
    rw [←relIndex_ker,QuotientGroup.ker_mk']
  have ho : Odd (Nat.card (E.map q)) := hcard.symm ▸ hodd
  obtain ⟨n,hn⟩ := (hA.map q).exists_card_dvd_pow
  have hcop : Nat.Coprime (Nat.card (A.map q)) (Nat.card (E.map q)) :=
    (ho.coprime_two_right.symm.pow_left n).coprime_dvd_left hn
  have hdis := Subgroup.disjoint_of_coprime_natCard hcop
  apply le_antisymm
  · intro x hx
    refine ⟨hx.1,?_⟩
    apply (QuotientGroup.eq_one_iff x).mp
    exact Subgroup.disjoint_def.mp hdis (mem_map_of_mem q hx.1) (mem_map_of_mem q hx.2)
  · exact inf_le_inf_left A hQE

/-- The image of an original reciprocal span under a homomorphism whose
kernel is an odd extension of Q has the same elementary structure and order
as its quotient by Q. The full kernel is not identified with Q. -/
theorem cubic_reciprocal_odd_kernel_actor_data
    {D : Type*} [Group D]
    (hb : 2 < sourceDistance h) {a c : Vertex T}
    (ha : color T a = false) (hc : color T c = false)
    (hd : (cosetGraph T).dist a c = 2)
    (hfixedC : ⁅V T c,Q T c⁆ ≤ fixedCore T c)
    (π : stabilizer T a →* D)
    (hQπ : (Q T a).subgroupOf (stabilizer T a) ≤ π.ker)
    (hodd : Odd (((Q T a).subgroupOf (stabilizer T a)).relIndex π.ker)) :
    let A := ((localZSpan T a c).subgroupOf (stabilizer T a)).map π
    IsElementaryAbelian 2 A ∧ Nat.card A = (Q T a).relIndex (localZSpan T a c) ∧
      (A = ⊥ ↔ localZSpan T a c ≤ Q T a) := by
  let := Q_normal T a
  let := finite_stabilizer T a
  let := cubic_reciprocal_actor_kernel_normal (h := h) hb ha hc hd
  let := cubic_reciprocal_actor_quotient_elementary_of_radius_fixed hb ha hc hd hfixedC
  let H := stabilizer T a
  let P := localZSpan T a c
  let N := (Q T a).subgroupOf P
  let A := (P.subgroupOf H).map π
  have hPH : P ≤ H := (localZSpan_le_Q T hc hd.le hb).trans
    (Q_le_stabilizer_of_dist_le_two c a hc ha (by rw [SimpleGraph.dist_comm,hd]))
  have hPtwo : IsPGroup 2 P :=
    (Q_isPGroup T h.relative_radical.isPGroup h.relative_radical.twoCore_le c hc).of_injective
      (inclusion (localZSpan_le_Q T hc hd.le hb)) (inclusion_injective _)
  have hinter := two_inf_odd_extension_eq (P.subgroupOf H) ((Q T a).subgroupOf H)
    π.ker hPtwo.comap_subtype hQπ hodd
  have hkpoint (x : P) : π ⟨x,hPH x.property⟩ = 1 ↔ (x : FreeAmalgam T) ∈ Q T a := by
    constructor
    · intro hx
      have hh : (⟨x,hPH x.property⟩ : H) ∈ P.subgroupOf H ⊓ π.ker := ⟨x.property,hx⟩
      rw [hinter] at hh
      exact hh.2
    · intro hx
      exact hQπ hx
  let f : P →* A := {
    toFun x := ⟨π ⟨x,hPH x.property⟩,⟨⟨x,hPH x.property⟩,x.property,rfl⟩⟩
    map_one' := by apply Subtype.ext; exact map_one π
    map_mul' x y := by
      apply Subtype.ext
      exact map_mul π (⟨x,hPH x.property⟩ : H) (⟨y,hPH y.property⟩ : H) }
  have hf : Function.Surjective f := by
    rintro ⟨y,x,hx,rfl⟩
    exact ⟨⟨x,hx⟩,rfl⟩
  have hk : f.ker = N := by
    ext x
    change f x = 1 ↔ (x : FreeAmalgam T) ∈ Q T a
    rw [Subtype.ext_iff]
    exact hkpoint x
  have hEA : IsElementaryAbelian 2 A := by
    let fbar : P ⧸ N →* A := QuotientGroup.lift N f hk.ge
    exact IsElementaryAbelian.of_surjective fbar
      (QuotientGroup.lift_surjective_of_surjective N f hf hk.ge)
  have hcard : Nat.card A = (Q T a).relIndex P := by
    have he := (Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective f hf).toEquiv).symm
    rw [hk] at he
    exact he
  refine ⟨hEA,hcard,?_⟩
  constructor
  · intro he x hx
    have hxA : π ⟨x,hPH hx⟩ ∈ A := ⟨⟨x,hPH hx⟩,hx,rfl⟩
    have hxone : π ⟨x,hPH hx⟩ = 1 := by
      change A = ⊥ at he
      rw [he] at hxA
      exact hxA
    exact (hkpoint ⟨x,hx⟩).mp hxone
  · intro hPQ
    apply bot_unique
    rintro y ⟨x,hx,rfl⟩
    exact hQπ (hPQ hx)

/-- A genuine odd-kernel actor satisfying the source index inequality is an
FF witness on the literal moving central quotient. -/
theorem cubic_reciprocal_central_ff_of_bound
    {D : Type*} [Group D] [Finite D]
    (hb : 2 < sourceDistance h) {a c : Vertex T}
    (ha : color T a = false) (hc : color T c = false)
    (hd : (cosetGraph T).dist a c = 2)
    (hfixedA : ⁅V T a,Q T a⁆ ≤ fixedCore T a)
    (hfixedC : ⁅V T c,Q T c⁆ ≤ fixedCore T c)
    (π : stabilizer T a →* D)
    (hQπ : (Q T a).subgroupOf (stabilizer T a) ≤ π.ker)
    (hodd : Odd (((Q T a).subgroupOf (stabilizer T a)).relIndex π.ker))
    (hne : ¬ localZSpan T a c ≤ Q T a) :
    letI := cubic_reciprocal_moving_quotient_elementary hb ha hfixedA
    ∀ (σ : Representation (ZMod 2) D (Additive ((Vcirc T a) ⧸ center (Vcirc T a)))),
      σ.comp π = Offenders.linearize (movingQuotientAction a) →
      2 ^ fixedCodim (Offenders.linearize (movingQuotientAction a))
        ((localZSpan T a c).subgroupOf (stabilizer T a)) ≤
          (Q T a).relIndex (localZSpan T a c) → IsFFModule σ := by
  let := cubic_reciprocal_moving_quotient_elementary hb ha hfixedA
  intro σ hact hi
  let A₀ := (localZSpan T a c).subgroupOf (stabilizer T a)
  let A := A₀.map π
  obtain ⟨hel,hcard,hbot⟩ := cubic_reciprocal_odd_kernel_actor_data hb ha hc hd
    hfixedC π hQπ hodd
  have hEA : IsElementaryTwo A := ⟨fun hh => hne (hbot.mp hh),hel⟩
  have hcod : fixedCodim (σ.comp π) A₀ = fixedCodim σ A := by
    unfold fixedCodim
    rw [fixedSpace_comp_map]
  rw [←hact,hcod,←hcard,hEA.card_eq_two_pow_rank] at hi
  exact ⟨A,hEA,(Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hi⟩

/-- Reciprocal source geometry forces an FF module at one of the two
vertices, once the actual actors descend through their retained odd kernels.
Both actions retain literal coordinates on Vcirc/center(Vcirc). -/
theorem cubic_reciprocal_central_ff_alternative
    {D₁ D₂ : Type*} [Group D₁] [Finite D₁] [Group D₂] [Finite D₂]
    (hb : 2 < sourceDistance h) {a c : Vertex T}
    (ha : color T a = false) (hc : color T c = false)
    (hd : (cosetGraph T).dist a c = 2)
    (hfixedA : ⁅V T a,Q T a⁆ ≤ fixedCore T a)
    (hfixedC : ⁅V T c,Q T c⁆ ≤ fixedCore T c)
    (hspanA : Vcirc T a ≤ localZSpan T c a ⊔ Z T a)
    (hspanC : Vcirc T c ≤ localZSpan T a c ⊔ Z T c)
    (hnonA : ⁅localZSpan T c a,localZSpan T c a⁆ ≠ ⊥)
    (hnonC : ⁅localZSpan T a c,localZSpan T a c⁆ ≠ ⊥)
    (πA : stabilizer T a →* D₁)
    (hQA : (Q T a).subgroupOf (stabilizer T a) ≤ πA.ker)
    (hoddA : Odd (((Q T a).subgroupOf (stabilizer T a)).relIndex πA.ker))
    (πC : stabilizer T c →* D₂)
    (hQC : (Q T c).subgroupOf (stabilizer T c) ≤ πC.ker)
    (hoddC : Odd (((Q T c).subgroupOf (stabilizer T c)).relIndex πC.ker)) :
    letI := cubic_reciprocal_moving_quotient_elementary hb ha hfixedA
    letI := cubic_reciprocal_moving_quotient_elementary hb hc hfixedC
    ∀ (σA : Representation (ZMod 2) D₁ (Additive ((Vcirc T a) ⧸ center (Vcirc T a))))
      (σC : Representation (ZMod 2) D₂ (Additive ((Vcirc T c) ⧸ center (Vcirc T c)))),
      σA.comp πA = Offenders.linearize (movingQuotientAction a) →
      σC.comp πC = Offenders.linearize (movingQuotientAction c) →
      IsFFModule σA ∨ IsFFModule σC := by
  let := cubic_reciprocal_moving_quotient_elementary hb ha hfixedA
  let := cubic_reciprocal_moving_quotient_elementary hb hc hfixedC
  intro σA σC hactA hactC
  have hiA := cubic_reciprocal_central_fixed_index_le hb ha hc hd hfixedA hfixedC hspanA
  have hiC := cubic_reciprocal_central_fixed_index_le hb hc ha
    (by rwa [SimpleGraph.dist_comm]) hfixedC hfixedA hspanC
  have hneA := cubic_reciprocal_nonabelian_span_not_le_seed_core hc hnonA
  have hneC := cubic_reciprocal_nonabelian_span_not_le_seed_core ha hnonC
  rcases le_total ((Q T c).relIndex (localZSpan T c a))
      ((Q T a).relIndex (localZSpan T a c)) with hi | hi
  · exact Or.inl (cubic_reciprocal_central_ff_of_bound hb ha hc hd hfixedA hfixedC
      πA hQA hoddA hneC σA hactA (hiA.trans hi))
  · exact Or.inr (cubic_reciprocal_central_ff_of_bound hb hc ha
      (by rwa [SimpleGraph.dist_comm]) hfixedC hfixedA
      πC hQC hoddC hneA σC hactC (hiC.trans hi))

private theorem cubic_reciprocal_span_nonabelian_of_moving_lower
    (hb : 2 < sourceDistance h) {a c : Vertex T}
    (ha : color T a = false) (hd : (cosetGraph T).dist a c = 2)
    (hspan : Vcirc T a ≤ localZSpan T c a ⊔ Z T a)
    (hlower : 2 < Nat.card (⁅Vcirc T a,Vcirc T a⁆ : Subgroup (FreeAmalgam T))) :
    ⁅localZSpan T c a,localZSpan T c a⁆ ≠ ⊥ := by
  intro hab
  let P := localZSpan T c a
  let Z₀ := Z T a
  have hVQ := (sourceGeometry h).V_le_Q hb a ha
  have hPQ : P ≤ Q T a :=
    (localZSpan_le_V T (by rw [SimpleGraph.dist_comm,hd])).trans hVQ
  have hZQ : Z₀ ≤ Q T a := (Z_le_VBall T a 2).trans hVQ
  have hZC : Z₀ ≤ centralizer (Q T a : Set (FreeAmalgam T)) :=
    commutator_eq_bot_iff_le_centralizer.mp (Z_centralizes_Q T a ha)
  have hZP : Z₀ ≤ centralizer (P : Set (FreeAmalgam T)) := hZC.trans (centralizer_le hPQ)
  have hZZ : Z₀ ≤ centralizer (Z₀ : Set (FreeAmalgam T)) := hZC.trans (centralizer_le hZQ)
  have hPP : P ≤ centralizer (P : Set (FreeAmalgam T)) :=
    commutator_eq_bot_iff_le_centralizer.mp hab
  have hPC : P ≤ centralizer (P ⊔ Z₀ : Subgroup (FreeAmalgam T)) :=
    le_centralizer_iff.mp (sup_le hPP hZP)
  have hZC' : Z₀ ≤ centralizer (P ⊔ Z₀ : Subgroup (FreeAmalgam T)) :=
    le_centralizer_iff.mp (sup_le (le_centralizer_iff.mp hZP) hZZ)
  have hzero : ⁅P ⊔ Z₀,P ⊔ Z₀⁆ = ⊥ :=
    commutator_eq_bot_iff_le_centralizer.mpr (sup_le hPC hZC')
  have hmzero : ⁅Vcirc T a,Vcirc T a⁆ = ⊥ :=
    le_bot_iff.mp ((commutator_mono hspan hspan).trans hzero.le)
  rw [hmzero,card_bot] at hlower
  omega

/-- The original reciprocal moving-radius lower bounds force both selected
spans to be nonabelian. Their seed supplements centralize the full radius,
so an abelian selected span would make the moving radius abelian. -/
theorem cubic_reciprocal_spans_nonabelian_of_moving_lower
    (hb : 2 < sourceDistance h) {a c : Vertex T}
    (ha : color T a = false) (hc : color T c = false)
    (hd : (cosetGraph T).dist a c = 2)
    (hspanA : Vcirc T a ≤ localZSpan T c a ⊔ Z T a)
    (hspanC : Vcirc T c ≤ localZSpan T a c ⊔ Z T c)
    (hlowerA : 2 < Nat.card (⁅Vcirc T a,Vcirc T a⁆ : Subgroup (FreeAmalgam T)))
    (hlowerC : 2 < Nat.card (⁅Vcirc T c,Vcirc T c⁆ : Subgroup (FreeAmalgam T))) :
    ⁅localZSpan T c a,localZSpan T c a⁆ ≠ ⊥ ∧
      ⁅localZSpan T a c,localZSpan T a c⁆ ≠ ⊥ := by
  exact ⟨cubic_reciprocal_span_nonabelian_of_moving_lower hb ha hd hspanA hlowerA,
    cubic_reciprocal_span_nonabelian_of_moving_lower hb hc
      (by rwa [SimpleGraph.dist_comm]) hspanC hlowerC⟩

end AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicFull
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
