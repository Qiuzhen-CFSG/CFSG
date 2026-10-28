module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.DistanceTwoRecognition.PairedImages

public import Theory.GroupAction.SubgroupQuotientFullAction
public import Theory.Representation.BinaryConjugationSection.FixedIndex
public import Theory.Representation.BinaryConjugationSection.QuadraticCommutator

/-!
# The literal secondary section and its paired action

The common edge center belongs to the maximal secondary seed. Transitivity
on neighbors therefore puts the whole endpoint Z-layer inside its orbit A.
The opposite-kernel intersection together with Z centralizes the opposite
orbit modulo Z. The order-q critical image in Z gives the exact q-factor
index estimate and bounds that quotient-centralizer index by q squared.

The Frattini bound makes the literal quotient A/Z elementary. Conjugation
descends through the actual local two-core quotient, retaining its original
component marking. Mutual normalization gives quadraticity of the opposite
secondary image. The index estimate becomes binary fixed codimension at
most 2n for this constructed section, with all central layers retained.

Source: MS93 (3.6), printed p.871. Nontrivial component action on A/Z,
sharp secondary-image orders, paired disjointness and natural recognition
still require proof. This does not establish the whole-core bound or the
field restriction in (3.7).
-/

public noncomputable section
open scoped IsMulCommutative
open Subgroup Theory.GroupTheory Representation
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.NormalizerTransfer
open CFSG.Quasithin.ChapterC.RankTwo.Sp4Four.CoreReconstruction
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.DistanceTwoRecognition

variable {M : Type*} [Group M] [Finite M] {T : Subgroup M}

private theorem secondary_seed_contains_edge (g : Geometry T) (hb : 0 < g.b T)
    {a z t : Vertex T} (ha : color T a = false) (hz : color T z = false)
    (hat : Adjacent T a t) (hzt : Adjacent T z t) :
    Z T t ≤ Sp4Four.secondarySeed T a t z := by
  apply (Sp4Four.secondarySeed_greatest T g hz hzt hb).2.2 _
    (Sp4Four.edge_Z_le_endpoint T hz hzt)
  have ht : color T t = true := by
    have hn := adjacent_color_ne T hat
    cases he : color T t <;> simp_all
  have hcomm : ⁅Z T t,Q T a⁆ = ⊥ := by
    apply commutator_eq_bot_iff_le_centralizer.mpr
    intro x hx y hy
    have hh : x ∈ omegaCenter (Q T t) := by
      simpa only [Z,ht,Bool.true_eq_false,↓reduceIte,edgeOmega] using hx
    exact (mem_omegaCenter_iff.mp hh).2.2 y (Q_le_adjacent_h T ht hat hy)
  exact hcomm.le.trans bot_le

/-- The full endpoint omega orbit is already contained in the secondary orbit. -/
theorem secondary_orbit_contains_Z (g : Geometry T) (hb : 0 < g.b T)
    {a z t : Vertex T} (ha : color T a = false) (hz : color T z = false)
    (hat : Adjacent T a t) (hzt : Adjacent T z t) :
    Z T a ≤ Sp4Four.secondaryOrbit T a (Sp4Four.secondarySeed T a t z) := by
  have hseed := secondary_seed_contains_edge g hb ha hz hat hzt
  rw [Z,if_pos ha]
  apply iSup_le
  intro u
  apply iSup_le
  intro hau
  obtain ⟨v,hv,hvt⟩ := stabilizer_transitive_neighbors T a hat hau
  have hu : color T u = true := by
    have hn := adjacent_color_ne T hau
    cases he : color T u <;> simp_all
  have he : edgeOmega T u = Z T u := by
    simp only [Z,hu,Bool.true_eq_false,↓reduceIte]
  rw [he,←hvt,Z_act]
  exact (map_mono hseed).trans (le_iSup (fun v : stabilizer T a =>
    rightConjugate (Sp4Four.secondarySeed T a t z) v) ⟨v,hv⟩)


private theorem index_with_normal_factor {G : Type*} [Group G]
    (A P Z : Subgroup G) (hZA : Z ≤ A) (hAP : A ≤ normalizer P) :
    P.relIndex Z * ((A ⊓ P) ⊔ Z).relIndex A = P.relIndex A := by
  let I := P.subgroupOf A
  let W := Z.subgroupOf A
  let : I.Normal := normal_subgroupOf_of_le_normalizer hAP
  have he : ((A ⊓ P) ⊔ Z).subgroupOf A = I ⊔ W := by
    rw [subgroupOf_sup (show A ⊓ P ≤ A from inf_le_left) hZA]
    exact congrArg (fun B : Subgroup A => B ⊔ W) (inf_subgroupOf_left P A)
  change _ * (((A ⊓ P) ⊔ Z).subgroupOf A).index = I.index
  rw [he]
  have hi : I.relIndex W = P.relIndex Z := relIndex_subgroupOf hZA
  rw [←hi,←relIndex_sup_left W I]
  exact relIndex_mul_index le_sup_left

variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

/-- The source quotient centralizer contains the entire opposite kernel
intersection together with Z, retaining both subgroups literally. -/
theorem replacement_paired_centralizer_contains
    {g : Geometry d.radical} {a z t : Vertex d.radical}
    (path : CriticalPath d.radical g a z) (hb : g.b d.radical = 2)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (hlarge : ¬ core d.radical a ≤
      (frattini (Q d.radical a)).map (Q d.radical a).subtype ⊔ X d.radical a) :
    let A := Sp4Four.secondaryOrbit d.radical a (Sp4Four.secondarySeed d.radical a t z)
    let A' := Sp4Four.secondaryOrbit d.radical z (Sp4Four.secondarySeed d.radical z t a)
    (A ⊓ Q d.radical z) ⊔ Z d.radical a ≤
      commutatorPreimage A A' (Z d.radical a) := by
  let A := Sp4Four.secondaryOrbit d.radical a (Sp4Four.secondarySeed d.radical a t z)
  let A' := Sp4Four.secondaryOrbit d.radical z (Sp4Four.secondarySeed d.radical z t a)
  have hpos : 0 < g.b d.radical := by omega
  have hedge := MSCentralOrbit.edgeCentralizerCondition d.radical (replacement_isPGroup h d)
    (replacement_core_le h d) (replacement_omegaOrbit_centralizer h d)
  let rev : CriticalPath d.radical g z a :=
    { start_color := path.end_color
      walk := path.walk.reverse
      shortest := by rw [SimpleGraph.Walk.length_reverse,path.shortest,SimpleGraph.dist_comm]
      critical := critical_reverse d.radical g hedge a path.start_color
        (by rw [g.distance_constant a path.start_color]; exact hpos)
        z path.end_color path.critical }
  have hlarge' : ¬ core d.radical z ≤
      (frattini (Q d.radical z)).map (Q d.radical z).subtype ⊔ X d.radical z := by
    obtain ⟨v,hv⟩ := exists_mVertex_of_color d.radical path.start_color
    have he : act d.radical v (alpha d.radical) = a := by
      rw [hv]
      simp only [alpha,act_mVertex,one_mul]
    have hbase := (nonfrattini_act_iff d.radical v (alpha d.radical)).mp
      (he.symm ▸ hlarge)
    exact nonfrattini_at_vertex d.radical hbase path.end_color
  obtain ⟨hAQ,_,_⟩ := replacement_secondary_orbit_bounds h d path hb hat hzt hlarge
  obtain ⟨hA'Q,_,_⟩ := replacement_secondary_orbit_bounds h d rev hb hzt hat hlarge'
  have hN' : ⁅A',Q d.radical z⁆ ≤ Z d.radical a :=
    ((replacement_secondary_commutator_eq_seed h d rev hb hzt hat hlarge').2.trans
      inf_le_left).trans (Sp4Four.edge_Z_le_endpoint d.radical path.start_color hat)
  have hZaA : Z d.radical a ≤ A :=
    secondary_orbit_contains_Z g (by omega) path.start_color path.end_color hat hzt
  apply sup_le
  · apply le_commutatorPreimage inf_le_left
    rw [commutator_comm]
    exact (commutator_mono le_rfl inf_le_right).trans hN'
  · apply le_commutatorPreimage hZaA
    apply le_normalizer_iff_commutator_le_left.mp
    exact (hA'Q.trans (Q_le_stabilizer_of_dist_two d.radical z a path.end_color (by
      rw [SimpleGraph.dist_comm,path.critical.1,g.distance_constant a path.start_color]
      exact hb))).trans (Z_normalized d.radical a)

/-- The order-q critical root is lost in the quotient centralizer index.
This is the source q-factor estimate before recognizing the secondary section. -/
theorem replacement_paired_centralizer_index
    {g : Geometry d.radical} {a z t : Vertex d.radical}
    (path : CriticalPath d.radical g a z) (hb : g.b d.radical = 2)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (hlarge : ¬ core d.radical a ≤
      (frattini (Q d.radical a)).map (Q d.radical a).subtype ⊔ X d.radical a) :
    let A := Sp4Four.secondaryOrbit d.radical a (Sp4Four.secondarySeed d.radical a t z)
    let A' := Sp4Four.secondaryOrbit d.radical z (Sp4Four.secondarySeed d.radical z t a)
    2^n * (commutatorPreimage A A' (Z d.radical a)).relIndex A ≤
      (Q d.radical z).relIndex A ∧
    (commutatorPreimage A A' (Z d.radical a)).relIndex A ≤ (2^n)^2 := by
  let A := Sp4Four.secondaryOrbit d.radical a (Sp4Four.secondarySeed d.radical a t z)
  let A' := Sp4Four.secondaryOrbit d.radical z (Sp4Four.secondarySeed d.radical z t a)
  let D := (A ⊓ Q d.radical z) ⊔ Z d.radical a
  let C := commutatorPreimage A A' (Z d.radical a)
  obtain ⟨hAQ,_,_⟩ := replacement_secondary_orbit_bounds h d path hb hat hzt hlarge
  let : Finite (stabilizer d.radical a) := finite_stabilizer d.radical a
  let : Finite A := Finite.of_injective
    (inclusion (hAQ.trans (show Q d.radical a ≤ stabilizer d.radical a from fun _ hx => hx.1)))
    (inclusion_injective _)
  have hAZ := secondary_orbit_contains_Z g (by omega) path.start_color path.end_color hat hzt
  have hn : A ≤ normalizer (Q d.radical z) :=
    (hAQ.trans (Q_le_stabilizer_of_dist_two d.radical a z path.start_color
      (path.critical.1.trans ((g.distance_constant a path.start_color).trans hb)))).trans
      (Q_normalized d.radical z)
  obtain ⟨_,_,hq,_,_,_⟩ := replacement_nonfrattini_root_actions h d path hb hlarge
  have hid : 2^n * D.relIndex A = (Q d.radical z).relIndex A := by
    rw [←hq]
    exact index_with_normal_factor A (Q d.radical z) (Z d.radical a) hAZ hn
  have hle : C.relIndex A ≤ D.relIndex A :=
    relIndex_le_of_le_left
      (replacement_paired_centralizer_contains h d path hb hat hzt hlarge)
      index_ne_zero_of_finite
  have hprod : 2^n * C.relIndex A ≤ (Q d.radical z).relIndex A :=
    (Nat.mul_le_mul_left _ hle).trans_eq hid
  refine ⟨hprod,?_⟩
  obtain ⟨_,_,_,_,_,hcard,hbound⟩ := replacement_secondary_image h d path hb hat hzt hlarge
  have hh : 2^n * C.relIndex A ≤ 2^n * (2^n)^2 := by
    calc
      _ ≤ (Q d.radical z).relIndex A := hprod
      _ ≤ (2^n)^3 := hcard ▸ hbound
      _ = _ := by ring
  exact Nat.le_of_mul_le_mul_left hh (by positivity)

/-- Z is relatively normal in the secondary orbit; the quotient is literal. -/
theorem replacement_secondary_quotient_normal
    {g : Geometry d.radical} {a z t : Vertex d.radical}
    (path : CriticalPath d.radical g a z) (hb : g.b d.radical = 2)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (hlarge : ¬ core d.radical a ≤
      (frattini (Q d.radical a)).map (Q d.radical a).subtype ⊔ X d.radical a) :
    let A := Sp4Four.secondaryOrbit d.radical a (Sp4Four.secondarySeed d.radical a t z)
    ((Z d.radical a).subgroupOf A).Normal := by
  obtain ⟨hAQ,_,_⟩ := replacement_secondary_orbit_bounds h d path hb hat hzt hlarge
  exact normal_subgroupOf_of_le_normalizer
    ((hAQ.trans (show Q d.radical a ≤ stabilizer d.radical a from fun _ hx => hx.1)).trans
      (Z_normalized d.radical a))

/-- The whole secondary quotient is elementary, without discarding Z or its
fixed central attachment. -/
theorem replacement_secondary_quotient_elementary
    {g : Geometry d.radical} {a z t : Vertex d.radical}
    (path : CriticalPath d.radical g a z) (hb : g.b d.radical = 2)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (hlarge : ¬ core d.radical a ≤
      (frattini (Q d.radical a)).map (Q d.radical a).subtype ⊔ X d.radical a) :
    let A := Sp4Four.secondaryOrbit d.radical a (Sp4Four.secondarySeed d.radical a t z)
    let := replacement_secondary_quotient_normal h d path hb hat hzt hlarge
    IsElementaryAbelian 2 (A ⧸ (Z d.radical a).subgroupOf A) := by
  let A := Sp4Four.secondaryOrbit d.radical a (Sp4Four.secondarySeed d.radical a t z)
  let N := (Z d.radical a).subgroupOf A
  let := replacement_secondary_quotient_normal h d path hb hat hzt hlarge
  obtain ⟨hAQ,_,hphi⟩ := replacement_secondary_orbit_bounds h d path hb hat hzt hlarge
  let : Finite (stabilizer d.radical a) := finite_stabilizer d.radical a
  let : Finite A := Finite.of_injective
    (inclusion (hAQ.trans (show Q d.radical a ≤ stabilizer d.radical a from fun _ hx => hx.1)))
    (inclusion_injective _)
  let : Fact (IsPGroup 2 A) := ⟨(Q_isPGroup d.radical (replacement_isPGroup h d)
    (replacement_core_le h d) a path.start_color).of_injective
      (inclusion hAQ) (inclusion_injective _)⟩
  have hpN : frattini A ≤ N := fun u hu => hphi (mem_map_of_mem A.subtype hu)
  exact {
    toIsMulCommutative := Normal.quotient_commutative_iff_commutator_le.mpr
      ((commutator_le_frattini_of_isPGroup (R := A) (p := 2)).trans hpN)
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (by
      intro x
      obtain ⟨u,rfl⟩ := QuotientGroup.mk'_surjective N x
      rw [←map_pow]
      exact (QuotientGroup.eq_one_iff _).mpr (hpN (pth_power_mem_frattini_of_isPGroup (p := 2) u))) }

/-- The original quotient group acts on the literal secondary quotient by
conjugation. The full local two-kernel is killed, rather than identified with
the kernel of the possibly nonfaithful secondary representation. -/
theorem replacement_secondary_quotient_action
    {g : Geometry d.radical} {a z t : Vertex d.radical}
    (path : CriticalPath d.radical g a z) (hb : g.b d.radical = 2)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (hlarge : ¬ core d.radical a ≤
      (frattini (Q d.radical a)).map (Q d.radical a).subtype ⊔ X d.radical a) :
    let A := Sp4Four.secondaryOrbit d.radical a (Sp4Four.secondarySeed d.radical a t z)
    let := replacement_secondary_quotient_normal h d path hb hat hzt hlarge
    let := replacement_secondary_quotient_elementary h d path hb hat hzt hlarge
    ∃ (κ : stabilizer d.radical a →* (d.overgroup ⧸ pCore 2 d.overgroup)),
      Function.Surjective κ ∧
      κ.ker.map (stabilizer d.radical a).subtype = Q d.radical a ∧
      ((Ltilde d.radical a).subgroupOf (stabilizer d.radical a)).map κ =
        replacementComponent d ∧
      ∃ (σ : Representation (ZMod 2) (d.overgroup ⧸ pCore 2 d.overgroup)
          (Additive (A ⧸ (Z d.radical a).subgroupOf A)))
        (c : BinaryConjugationSection (stabilizer d.radical a) A (Z d.radical a) (σ.comp κ)),
        ∀ u : A, (c.coordinates u).toAdd =
          Additive.ofMul (QuotientGroup.mk' ((Z d.radical a).subgroupOf A) u) := by
  let A := Sp4Four.secondaryOrbit d.radical a (Sp4Four.secondarySeed d.radical a t z)
  let S := stabilizer d.radical a
  let N := (Z d.radical a).subgroupOf A
  let := replacement_secondary_quotient_normal h d path hb hat hzt hlarge
  let := replacement_secondary_quotient_elementary h d path hb hat hzt hlarge
  obtain ⟨hAQ,hcomm,_⟩ := replacement_secondary_orbit_bounds h d path hb hat hzt hlarge
  have hn : S ≤ normalizer A := conjugatesIn_normalized _ _
  obtain ⟨α,hα⟩ := exists_quotient_conjugation_action S A (Z d.radical a) hn
    (Z_normalized d.radical a) inferInstance
  have hkill := quotient_conjugation_action_kills_commutator_layer S A
    (Z d.radical a) (Q d.radical a) inferInstance hn hcomm α hα
  obtain ⟨⟨E,hE,e,hcover,j,hj,hjU,κ,hκ,hk,hkC,him,hfaith,hsemi,hact,hproj,hker⟩⟩ :=
    replacement_ambient_initial_cover_at_vertex h d path.start_color
  have hκker : κ.ker ≤ α.ker := by
    intro x hx
    apply hkill
    exact hk ▸ mem_map_of_mem S.subtype hx
  let β : (d.overgroup ⧸ pCore 2 d.overgroup) →* MulAut (A ⧸ N) :=
    κ.liftOfSurjective hκ ⟨α,hκker⟩
  have hβ (s : S) : β (κ s) = α s :=
    κ.liftOfRightInverse_comp_apply (Function.surjInv hκ)
      (Function.rightInverse_surjInv hκ) ⟨α,hκker⟩ s
  let σ : Representation (ZMod 2) (d.overgroup ⧸ pCore 2 d.overgroup)
      (Additive (A ⧸ N)) := {
    toFun := fun x => (β x).toMonoidHom.toAdditive.toZModLinearMap 2
    map_one' := by
      ext v
      change β 1 v.toMul = v.toMul
      rw [map_one]
      rfl
    map_mul' := by
      intro x y
      ext v
      change β (x*y) v.toMul = β x (β y v.toMul)
      rw [map_mul]
      rfl }
  let q := QuotientGroup.mk' N
  let π : A →* Multiplicative (Additive (A ⧸ N)) := {
    toFun := fun u => Multiplicative.ofAdd (Additive.ofMul (q u))
    map_one' := q.map_one
    map_mul' := q.map_mul }
  have hπ : Function.Surjective π := by
    intro v
    obtain ⟨u,hu⟩ := QuotientGroup.mk'_surjective N v.toAdd.toMul
    exact ⟨u,hu⟩
  let c : BinaryConjugationSection S A (Z d.radical a) (σ.comp κ) := {
    section_le := hAQ.trans (fun _ hx => hx.1)
    kernel_le := secondary_orbit_contains_Z g (by omega) path.start_color path.end_color hat hzt
    normalized := hn
    coordinates := π
    onto := hπ
    kernel_eq := by ext u; exact QuotientGroup.eq_one_iff u
    equivariant := by
      intro s u
      change q _ = β (κ s) (q u)
      rw [hβ]
      exact (hα s u).symm }
  exact ⟨κ,hκ,hk,him,σ,c,fun _ => rfl⟩

omit h in
private theorem relative_fixed_index {G : Type*} [Group G]
    {S A Z : Subgroup G} {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    {ρ : Representation (ZMod 2) S V} [Finite A]
    (c : BinaryConjugationSection S A Z ρ)
    (P : Subgroup G) (hPS : P ≤ S)
    (hAZ : A ≤ normalizer Z) (hPZ : P ≤ normalizer Z) :
    (commutatorPreimage A P Z).relIndex A =
      2 ^ Representation.BinaryOffender.fixedCodim ρ (P.subgroupOf S) := by
  let : Finite V := Finite.of_surjective (fun u : A => (c.coordinates u).toAdd)
    (Multiplicative.toAdd.surjective.comp c.onto)
  let C := commutatorPreimage A P Z
  let B : Subgroup (Multiplicative V) := AddSubgroup.toSubgroup'
    (Representation.BinaryOffender.fixedSpace ρ (P.subgroupOf S)).toAddSubgroup
  have hm : (C.subgroupOf A).map c.coordinates = B := by
    ext v
    change v.toAdd ∈ c.imageSpace C ↔ v.toAdd ∈
      Representation.BinaryOffender.fixedSpace ρ (P.subgroupOf S)
    rw [c.fixed_image_eq P hPS hAZ]
  have hz : Z ≤ C := le_commutatorPreimage c.kernel_le
    (le_normalizer_iff_commutator_le_left.mp hPZ)
  have hk : c.coordinates.ker ≤ C.subgroupOf A := by
    rw [c.kernel_eq]
    exact comap_mono hz
  have hi : B.index = C.relIndex A := by
    rw [←hm,index_map_eq _ c.onto hk]
    rfl
  have hc := B.card_mul_index
  have hB : Nat.card B = 2 ^ Module.finrank (ZMod 2)
      (Representation.BinaryOffender.fixedSpace ρ (P.subgroupOf S)) := by
    exact (Module.natCard_eq_pow_finrank (K := ZMod 2)
      (V := Representation.BinaryOffender.fixedSpace ρ (P.subgroupOf S))).trans
        (by rw [Nat.card_zmod])
  have hV : Nat.card (Multiplicative V) = 2 ^ Module.finrank (ZMod 2) V := by
    exact (Module.natCard_eq_pow_finrank (K := ZMod 2) (V := V)).trans
      (by rw [Nat.card_zmod])
  rw [hB,hV,←Representation.BinaryOffender.fixedCodim_add_finrank ρ
    (P.subgroupOf S),add_comm,pow_add] at hc
  exact hi.symm.trans (Nat.eq_of_mul_eq_mul_left (by positivity) hc)

/-- The q-factor estimate becomes an actual fixed codimension bound on the
constructed secondary representation. It holds for every choice of its
quotient coordinates, preserving the original actor image. -/
theorem replacement_secondary_fixed_codimension
    {g : Geometry d.radical} {a z t : Vertex d.radical}
    (path : CriticalPath d.radical g a z) (hb : g.b d.radical = 2)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (hlarge : ¬ core d.radical a ≤
      (frattini (Q d.radical a)).map (Q d.radical a).subtype ⊔ X d.radical a)
    {J V : Type*} [Group J] [AddCommGroup V] [Module (ZMod 2) V]
    (κ : stabilizer d.radical a →* J) (σ : Representation (ZMod 2) J V)
    (c : BinaryConjugationSection (stabilizer d.radical a)
      (Sp4Four.secondaryOrbit d.radical a (Sp4Four.secondarySeed d.radical a t z))
      (Z d.radical a) (σ.comp κ)) :
    let A' := Sp4Four.secondaryOrbit d.radical z (Sp4Four.secondarySeed d.radical z t a)
    Representation.BinaryOffender.fixedCodim σ
      ((A'.subgroupOf (stabilizer d.radical a)).map κ) ≤ 2*n := by
  let A := Sp4Four.secondaryOrbit d.radical a (Sp4Four.secondarySeed d.radical a t z)
  let A' := Sp4Four.secondaryOrbit d.radical z (Sp4Four.secondarySeed d.radical z t a)
  let S := stabilizer d.radical a
  have hpos : 0 < g.b d.radical := by omega
  have hedge := MSCentralOrbit.edgeCentralizerCondition d.radical (replacement_isPGroup h d)
    (replacement_core_le h d) (replacement_omegaOrbit_centralizer h d)
  let rev : CriticalPath d.radical g z a :=
    { start_color := path.end_color
      walk := path.walk.reverse
      shortest := by rw [SimpleGraph.Walk.length_reverse,path.shortest,SimpleGraph.dist_comm]
      critical := critical_reverse d.radical g hedge a path.start_color
        (by rw [g.distance_constant a path.start_color]; exact hpos)
        z path.end_color path.critical }
  have hlarge' : ¬ core d.radical z ≤
      (frattini (Q d.radical z)).map (Q d.radical z).subtype ⊔ X d.radical z := by
    obtain ⟨v,hv⟩ := exists_mVertex_of_color d.radical path.start_color
    have he : act d.radical v (alpha d.radical) = a := by
      rw [hv]
      simp only [alpha,act_mVertex,one_mul]
    exact nonfrattini_at_vertex d.radical
      ((nonfrattini_act_iff d.radical v (alpha d.radical)).mp (he.symm ▸ hlarge))
      path.end_color
  have hA'Q := (replacement_secondary_orbit_bounds h d rev hb hzt hat hlarge').1
  have hA'S : A' ≤ S := hA'Q.trans
    (Q_le_stabilizer_of_dist_two d.radical z a path.end_color (by
      rw [SimpleGraph.dist_comm,path.critical.1,g.distance_constant a path.start_color]
      exact hb))
  let : Finite S := finite_stabilizer d.radical a
  let : Finite A := Finite.of_injective (inclusion c.section_le) (inclusion_injective _)
  have he := relative_fixed_index c A' hA'S
    (c.section_le.trans (Z_normalized d.radical a))
    (hA'S.trans (Z_normalized d.radical a))
  have hfix : Representation.BinaryOffender.fixedCodim (σ.comp κ) (A'.subgroupOf S) =
      Representation.BinaryOffender.fixedCodim σ ((A'.subgroupOf S).map κ) := by
    unfold Representation.BinaryOffender.fixedCodim
    rw [Representation.BinaryOffender.fixedSpace_comp_map]
  rw [hfix] at he
  have hidx := (replacement_paired_centralizer_index h d path hb hat hzt hlarge).2
  rw [he,←pow_mul,Nat.mul_comm n 2] at hidx
  exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hidx

/-- The opposite secondary orbit acts quadratically on the actual secondary
section, with the whole Z-layer as its kernel. -/
theorem replacement_secondary_quadratic
    {g : Geometry d.radical} {a z t : Vertex d.radical}
    (path : CriticalPath d.radical g a z) (hb : g.b d.radical = 2)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (hlarge : ¬ core d.radical a ≤
      (frattini (Q d.radical a)).map (Q d.radical a).subtype ⊔ X d.radical a)
    {J V : Type*} [Group J] [AddCommGroup V] [Module (ZMod 2) V]
    (κ : stabilizer d.radical a →* J) (σ : Representation (ZMod 2) J V)
    (c : BinaryConjugationSection (stabilizer d.radical a)
      (Sp4Four.secondaryOrbit d.radical a (Sp4Four.secondarySeed d.radical a t z))
      (Z d.radical a) (σ.comp κ)) :
    let A' := Sp4Four.secondaryOrbit d.radical z (Sp4Four.secondarySeed d.radical z t a)
    Representation.BinaryOffender.IsQuadratic σ
      ((A'.subgroupOf (stabilizer d.radical a)).map κ) := by
  let A := Sp4Four.secondaryOrbit d.radical a (Sp4Four.secondarySeed d.radical a t z)
  let A' := Sp4Four.secondaryOrbit d.radical z (Sp4Four.secondarySeed d.radical z t a)
  have hpos : 0 < g.b d.radical := by omega
  have hedge := MSCentralOrbit.edgeCentralizerCondition d.radical (replacement_isPGroup h d)
    (replacement_core_le h d) (replacement_omegaOrbit_centralizer h d)
  let rev : CriticalPath d.radical g z a :=
    { start_color := path.end_color
      walk := path.walk.reverse
      shortest := by rw [SimpleGraph.Walk.length_reverse,path.shortest,SimpleGraph.dist_comm]
      critical := critical_reverse d.radical g hedge a path.start_color
        (by rw [g.distance_constant a path.start_color]; exact hpos)
        z path.end_color path.critical }
  have hlarge' : ¬ core d.radical z ≤
      (frattini (Q d.radical z)).map (Q d.radical z).subtype ⊔ X d.radical z := by
    obtain ⟨v,hv⟩ := exists_mVertex_of_color d.radical path.start_color
    have he : act d.radical v (alpha d.radical) = a := by
      rw [hv]
      simp only [alpha,act_mVertex,one_mul]
    exact nonfrattini_at_vertex d.radical
      ((nonfrattini_act_iff d.radical v (alpha d.radical)).mp (he.symm ▸ hlarge))
      path.end_color
  have hAQ := (replacement_secondary_orbit_bounds h d path hb hat hzt hlarge).1
  have hAS : A ≤ stabilizer d.radical z := hAQ.trans
    (Q_le_stabilizer_of_dist_two d.radical a z path.start_color
      (path.critical.1.trans ((g.distance_constant a path.start_color).trans hb)))
  have hA'Q := (replacement_secondary_orbit_bounds h d rev hb hzt hat hlarge').1
  have hcross : ⁅A',A⁆ ≤ A' := le_normalizer_iff_commutator_le_left.mp
    (hAS.trans (conjugatesIn_normalized _ _))
  have hN' : ⁅A',Q d.radical z⁆ ≤ Z d.radical a :=
    ((replacement_secondary_commutator_eq_seed h d rev hb hzt hat hlarge').2.trans
      inf_le_left).trans (Sp4Four.edge_Z_le_endpoint d.radical path.start_color hat)
  apply BinaryConjugationSection.isQuadratic_of_triple_commutator_le
    (stabilizer d.radical a) A (Z d.radical a) A' σ κ c
  exact (commutator_mono le_rfl (hcross.trans hA'Q)).trans hN'

/-- Construct the actual elementary secondary section, its original local
quotient marking, and its quadratic opposite action of binary codimension at
most 2n. Every action and coordinate premise is discharged here. The source's
nontrivial component action and natural-section recognition remain separate. -/
theorem replacement_secondary_section
    {g : Geometry d.radical} {a z t : Vertex d.radical}
    (path : CriticalPath d.radical g a z) (hb : g.b d.radical = 2)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (hlarge : ¬ core d.radical a ≤
      (frattini (Q d.radical a)).map (Q d.radical a).subtype ⊔ X d.radical a) :
    let A := Sp4Four.secondaryOrbit d.radical a (Sp4Four.secondarySeed d.radical a t z)
    let A' := Sp4Four.secondaryOrbit d.radical z (Sp4Four.secondarySeed d.radical z t a)
    let := replacement_secondary_quotient_normal h d path hb hat hzt hlarge
    let := replacement_secondary_quotient_elementary h d path hb hat hzt hlarge
    ∃ (κ : stabilizer d.radical a →* (d.overgroup ⧸ pCore 2 d.overgroup)),
      Function.Surjective κ ∧
      κ.ker.map (stabilizer d.radical a).subtype = Q d.radical a ∧
      ((Ltilde d.radical a).subgroupOf (stabilizer d.radical a)).map κ =
        replacementComponent d ∧
      ∃ (σ : Representation (ZMod 2) (d.overgroup ⧸ pCore 2 d.overgroup)
          (Additive (A ⧸ (Z d.radical a).subgroupOf A)))
        (c : BinaryConjugationSection (stabilizer d.radical a) A (Z d.radical a) (σ.comp κ)),
        (∀ u : A, (c.coordinates u).toAdd =
          Additive.ofMul (QuotientGroup.mk' ((Z d.radical a).subgroupOf A) u)) ∧
        Representation.BinaryOffender.IsQuadratic σ
          ((A'.subgroupOf (stabilizer d.radical a)).map κ) ∧
        Representation.BinaryOffender.fixedCodim σ
          ((A'.subgroupOf (stabilizer d.radical a)).map κ) ≤ 2*n := by
  let := replacement_secondary_quotient_normal h d path hb hat hzt hlarge
  let := replacement_secondary_quotient_elementary h d path hb hat hzt hlarge
  obtain ⟨κ,hκ,hk,hL,σ,c,hc⟩ :=
    replacement_secondary_quotient_action h d path hb hat hzt hlarge
  refine ⟨κ,hκ,hk,hL,σ,c,hc,?_,?_⟩
  · exact replacement_secondary_quadratic h d path hb hat hzt hlarge κ σ c
  · exact replacement_secondary_fixed_codimension h d path hb hat hzt hlarge κ σ c

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.DistanceTwoRecognition
