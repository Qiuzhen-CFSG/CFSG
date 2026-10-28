module
public import CFSG.Quasithin.ChapterF.Section04.UnitarySource.FourTorus
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitarySource.LongFixed
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitarySource.OddRecognition
public import Theory.GroupTheory.Hall.ConjugateTorusConstruction

/-!
# Splitting the full prepared U₄ Sylow over its inner intersection

The fixed-field torus is transported through the actual reduced overlap.
Its odd parameter group lies in an odd Hall subgroup. A two-element in the
inner Sylow normalizing this Hall subgroup centralizes it, hence is trivial
by the native torus calculation. Hall conjugacy constructs a complement
inside the original T. The faithful quotient-field coefficient makes this
complement cyclic of order [T:T∩L]. Thus a proper inner Sylow supplies an
actual outer involution for ordinary and degree-two comparisons alike.

The sourceS subgroup is not substituted for the inner Sylow. When T is
inner, the same marked extension has odd outer index and the proved
F.4.43 comparison yields recognition. Otherwise the constructed involution
feeds the actual ambient normalizer-growth argument. This leaves the
nontrivial invariant long-root intersection in that full fixed centralizer
as the remaining obstruction; no graph marking is assigned to the maximizer.

Source: Aschbacher–Smith F.4.29(2),37–38 and 5.3.3, printed pp.289,293–294,659
of `refs/quasithin.pdf`. Both orientations, q=4 and all original inputs remain.
-/

public noncomputable section
open Subgroup Subgroup.OddHall Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
open ChapterF.GreenBook.LieModels.UnitaryFour UnitaryCompletion
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L W H A C : Subgroup G} {n : ℕ}

omit [Finite G] in
private theorem parabolic_normalized {S : Subgroup G} {J : Fin 2 → Subgroup G}
    (hTS : (T : Subgroup G) ≤ normalizer (S : Set G))
    (hTJ : ∀ i, (T : Subgroup G) ≤ normalizer (J i : Set G)) (i : Fin 2) :
    (T : Subgroup G) ≤ normalizer (ChapterF.Source.parabolic J S i : Set G) := by
  have hb (j : Fin 2) : (T : Subgroup G) ≤ normalizer (ChapterF.Source.borel (J j) S : Set G) := by
    have hi := (le_inf hTS (hTJ j)).trans inf_normalizer_le_normalizer_inf
    exact (le_inf (hTJ j) (hi.trans (normalizer _).le_normalizer)).trans
      inf_normalizer_le_normalizer_inf
  exact (le_inf ((le_inf (hTJ i) hTS).trans (normalizer_inf_normalizer_le_normalizer_sup _ _))
    (hb (ChapterF.Source.other i))).trans (normalizer_inf_normalizer_le_normalizer_sup _ _)

variable (d : Preparation T L H A C (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H)) (m : ℕ) (hm : 1 ≤ m)
    (hc : FourLocalComparison L (residual H) (sourceS L H) m hm)
include d h hH hp hm hc

private theorem reduced_borel_setup
    (e : (ChapterF.Source.parabolic ![L,residual H] ((T : Subgroup G) ⊓ L) 0 ⊓
      ChapterF.Source.parabolic ![L,residual H] ((T : Subgroup G) ⊓ L) 1 : Subgroup G) ≃* overlap m hm) :
    let B := ChapterF.Source.parabolic ![L,residual H] ((T : Subgroup G) ⊓ L) 0 ⊓
      ChapterF.Source.parabolic ![L,residual H] ((T : Subgroup G) ⊓ L) 1
    Group.IsSolvable B ∧ (T : Subgroup G) ≤ normalizer (B : Set G) ∧
      B ≤ normalizer (((T : Subgroup G) ⊓ L : Subgroup G) : Set G) ∧
      ∃ P : Sylow 2 B, (P : Subgroup B).map B.subtype = (T : Subgroup G) ⊓ L := by
  let R := (T : Subgroup G) ⊓ L
  let B := ChapterF.Source.parabolic ![L,residual H] R 0 ⊓
    ChapterF.Source.parabolic ![L,residual H] R 1
  have hRB : R ≤ B := le_inf (le_sup_right.trans le_sup_left) (le_sup_right.trans le_sup_left)
  have hTR : (T : Subgroup G) ≤ normalizer (R : Set G) :=
    (le_inf (T : Subgroup G).le_normalizer h.sylow_normalizes).trans inf_normalizer_le_normalizer_inf
  have hTK (i : Fin 2) : (T : Subgroup G) ≤ normalizer (![L,residual H] i : Set G) := by
    fin_cases i
    · exact h.sylow_normalizes
    · exact hH.1.1.2.trans (le_normalizer_residual H)
  have hTB : (T : Subgroup G) ≤ normalizer (B : Set G) :=
    (le_inf (parabolic_normalized hTR hTK 0) (parabolic_normalized hTR hTK 1)).trans
      inf_normalizer_le_normalizer_inf
  let Q₀ := (projectiveSylow m hm).subtype (upperProjective_le_overlap m hm)
  let Q := Q₀.mapSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  have hQ : (Q : Subgroup B) = pCore 2 B := by
    change ((upperProjective m hm).subgroupOf (overlap m hm)).map e.symm.toMonoidHom = _
    rw [←overlap_twoCore,pCore_map_iso]
  have hcoreT : B.pCoreIn 2 ≤ (T : Subgroup G) := by
    have hn := hTB.trans (normalizer_le_normalizer_characteristic_image B (pCore 2 B))
    exact le_sup_right.trans_eq (T.is_maximal'
      (T.isPGroup'.to_sup_of_normal_right' (isPGroup_pCoreIn 2 B) hn) le_sup_left)
  have hcoreR : B.pCoreIn 2 = R := by
    apply le_antisymm
    · exact (le_inf hcoreT (pCoreIn_le 2 B)).trans_eq
        (d.unitary_reduced_overlap_sylow h hH hp m hm hc)
    · obtain ⟨P,hP⟩ := (T.isPGroup'.comap_subtype (K := B)).exists_le_sylow
      have hQP : (Q : Subgroup B) ≤ P := hQ ▸ pCore_isPGroup.le_sylow_of_normal P
      have hPQ : (P : Subgroup B) = Q := Q.is_maximal' P.isPGroup' hQP
      intro x hx
      apply mem_map_of_mem B.subtype (x := ⟨x,hRB hx⟩)
      rw [←hQ,←hPQ]
      exact hP hx.1
  have hsol : Group.IsSolvable B := by
    let := overlap_isSolvable m hm
    exact Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective
  refine ⟨hsol,hTB,?_,Q,?_⟩
  · change B ≤ normalizer (R : Set G)
    rw [←hcoreR]
    exact B.le_normalizer.trans (normalizer_le_normalizer_characteristic_image B (pCore 2 B))
  · rw [hQ]
    exact hcoreR

/-- A Hall subgroup containing the literal fixed-field torus gives a
complement to the original inner Sylow, for ordinary and degree-two rows. -/
theorem Preparation.unitaryFour_torus_split_of_overlap_equiv
    (e : (ChapterF.Source.parabolic ![L,residual H] ((T : Subgroup G) ⊓ L) 0 ⊓
      ChapterF.Source.parabolic ![L,residual H] ((T : Subgroup G) ⊓ L) 1 : Subgroup G) ≃* overlap m hm) :
    let R := (T : Subgroup G) ⊓ L
    let B := ChapterF.Source.parabolic ![L,residual H] R 0 ⊓
      ChapterF.Source.parabolic ![L,residual H] R 1
    ∃ D : Subgroup G, D ≤ B ∧ IsHallSubgroup oddPrimes (D.subgroupOf B) ∧
      (B.subtype.comp (e.symm.toMonoidHom.comp (ChapterF.UnitarySource.FourTorus.flagTorus m hm))).range ≤ D ∧
      Disjoint R (normalizer (D : Set G)) ∧
      (T : Set G) = (R : Set G) *
        ((T : Subgroup G) ⊓ normalizer (D : Set G) : Set G) := by
  let R := (T : Subgroup G) ⊓ L
  let B := ChapterF.Source.parabolic ![L,residual H] R 0 ⊓
    ChapterF.Source.parabolic ![L,residual H] R 1
  have hRB : R ≤ B := le_inf (le_sup_right.trans le_sup_left) (le_sup_right.trans le_sup_left)
  obtain ⟨hsol,hTB,hBR,P,hP⟩ := reduced_borel_setup d h hH hp m hm hc e
  let tau := ChapterF.UnitarySource.FourTorus.flagTorus m hm
  let rho := B.subtype.comp (e.symm.toMonoidHom.comp tau)
  have hRho : rho.range ≤ B := by rintro _ ⟨x,rfl⟩; exact (e.symm (tau x)).property
  have ho : Odd (Nat.card rho.range) :=
    (ChapterF.UnitarySource.FourTorus.flagTorus_parameter_odd m hm).of_dvd_nat (card_range_dvd rho)
  obtain ⟨D,hRD,hDB,hHall⟩ := exists_hall_containing_odd B rho.range hsol hRho ho
  have hodd : ¬ 2 ∣ Nat.card D := by
    intro hd
    apply hHall.p_in_pi_of_p_dvd_card ⟨2,Nat.prime_two⟩ _ rfl
    rwa [Nat.card_congr (subgroupOfEquivOfLe hDB).toEquiv]
  have hdis : Disjoint R D := by
    obtain ⟨k,hk⟩ := (T.isPGroup'.to_le (show R ≤ (T : Subgroup G) from inf_le_left)).exists_card_eq
    apply disjoint_of_coprime_natCard
    rw [hk]
    exact (Nat.prime_two.coprime_iff_not_dvd.mpr hodd).pow_left k
  have hdisN : Disjoint R (normalizer (D : Set G)) := by
    apply disjoint_def.mpr
    intro x hx hn
    have hcomm (y : G) (hy : y ∈ D) : Commute x y := by
      have hzD : x*y*x⁻¹*y⁻¹ ∈ D := D.mul_mem
        ((mem_normalizer_iff.mp hn y).mp hy) (D.inv_mem hy)
      have hzR : x*y*x⁻¹*y⁻¹ ∈ R := by
        have hh := R.mul_mem hx
          ((mem_normalizer_iff.mp (hBR (hDB hy)) x⁻¹).mp (R.inv_mem hx))
        simpa only [mul_assoc] using hh
      have hz := disjoint_def.mp hdis hzR hzD
      calc
        x*y = (x*y*x⁻¹*y⁻¹)*(y*x) := by group
        _ = y*x := by rw [hz,one_mul]
    let xb : B := ⟨x,hRB hx⟩
    obtain ⟨k,hk⟩ := T.isPGroup'.exists_pow_pow_eq_one ⟨x,hx.1⟩
    have hxp : (e xb).val^(2^k)=1 := by
      have hh : xb^(2^k)=1 := Subtype.ext (congrArg (fun z : T => z.val) hk)
      exact congrArg Subtype.val ((map_pow e xb (2^k)).symm.trans
        ((congrArg e hh).trans e.map_one))
    have hxt (a : (PointLocal.FixedField m)ˣ × (PointLocal.FixedField m)ˣ) :
        Commute (e xb).val (tau a).val := by
      let y := e.symm (tau a)
      have hxy : Commute xb y := Subtype.ext (hcomm y.val (hRD ⟨a,rfl⟩))
      have hh := hxy.map e.toMonoidHom
      change Commute (e xb) (e y) at hh
      dsimp only [y] at hh
      rw [e.apply_symm_apply] at hh
      exact hh.map (overlap m hm).subtype
    have hxe := ChapterF.UnitarySource.FourTorus.projective_two_element_centralizer m hm
      (d.unitary_reduced_native_comparison h hH.1.1.2 hp m hm hc).1 (e xb).val k hxp hxt
    have hxb : xb=1 := e.injective ((Subtype.ext hxe).trans e.map_one.symm)
    exact congrArg Subtype.val hxb
  exact ⟨D,hDB,hHall,hRD,hdisN,normal_sylow_frattini B R (T : Subgroup G) D
    hsol inf_le_left hTB P hP hDB hHall⟩

/-- The full original T splits over T∩L, including ordinary even exponents
and the genuine degree-two source comparison. -/
theorem Preparation.unitaryFour_sylow_complement :
    ∃ B : Subgroup G, B ≤ (T : Subgroup G) ∧ Disjoint ((T : Subgroup G) ⊓ L) B ∧
      (T : Set G) = (((T : Subgroup G) ⊓ L : Subgroup G) : Set G) * (B : Set G) ∧
      IsCyclic B ∧ Nat.card B = L.relIndex (T : Subgroup G) := by
  obtain ⟨_,_,hc'⟩ := d.unitary_reduced_native_comparison h hH.1.1.2 hp m hm hc
  have he : Nonempty ((ChapterF.Source.parabolic ![L,residual H] ((T : Subgroup G) ⊓ L) 0 ⊓
      ChapterF.Source.parabolic ![L,residual H] ((T : Subgroup G) ⊓ L) 1 : Subgroup G) ≃* overlap m hm) :=
    hc'.elim (fun ⟨e⟩ => ⟨e.middle⟩) (fun ⟨e⟩ => ⟨e.middle⟩)
  obtain ⟨D,_,_,_,hdis,hsplit⟩ := d.unitaryFour_torus_split_of_overlap_equiv h hH hp m hm hc he.some
  let R := (T : Subgroup G) ⊓ L
  let B := (T : Subgroup G) ⊓ normalizer (D : Set G)
  have hBT : B ≤ (T : Subgroup G) := inf_le_left
  have hd : Disjoint R B := hdis.mono_right inf_le_right
  have hcomp : IsComplement' (R.subgroupOf (T : Subgroup G))
      (B.subgroupOf (T : Subgroup G)) := by
    apply isComplement'_of_disjoint_and_mul_eq_univ
    · apply disjoint_def.mpr
      intro x hx hy
      exact Subtype.ext (disjoint_def.mp hd hx hy)
    · apply Set.eq_univ_iff_forall.mpr
      intro x
      have hx : x.val ∈ (R : Set G) * (B : Set G) := hsplit ▸ x.property
      obtain ⟨s,hs,b,hb,he⟩ := hx
      exact ⟨⟨s,hs.1⟩,hs,⟨b,hBT hb⟩,hb,Subtype.ext he⟩
  refine ⟨B,hBT,hd,hsplit,?_,?_⟩
  · obtain ⟨F,_,_,hF,⟨e⟩⟩ := h.linear
    let := Fintype.ofFinite F
    let : CharP F 2 := charP_of_card_eq_prime_pow
      (by simpa only [Nat.card_eq_fintype_card] using hF)
    let : IsCyclic (F ≃+* F) := Theory.PSL2.OuterSolvable.finiteFieldAut_isCyclic
    let phi := (unitaryFourSylowFieldAction h.sylow_normalizes e).comp (inclusion hBT)
    apply isCyclic_of_injective phi
    apply (MonoidHom.ker_eq_bot_iff phi).mp
    apply bot_unique
    intro x hx
    have hxL : x.val ∈ L := by
      have hh : inclusion hBT x ∈ (unitaryFourSylowFieldAction h.sylow_normalizes e).ker := hx
      rw [d.unitaryFour_sylow_field_kernel h hH hp m hm hc e] at hh
      exact hh
    exact Subtype.ext (disjoint_def.mp hd ⟨hBT x.property,hxL⟩ x.property)
  · rw [←Nat.card_congr (subgroupOfEquivOfLe hBT).toEquiv]
    have he : R.subgroupOf (T : Subgroup G) = L.subgroupOf (T : Subgroup G) := by
      ext x; exact and_iff_right x.property
    change Nat.card (B.subgroupOf (T : Subgroup G)) = (L.subgroupOf (T : Subgroup G)).index
    rw [←he]
    exact hcomp.symm.index_eq_card.symm

/-- A proper inner Sylow supplies an actual outer involution; the cyclic
quotient alone is not used as a splitting assumption. -/
theorem Preparation.unitaryFour_exists_outer_involution
    (hST : (T : Subgroup G) ⊓ L < (T : Subgroup G)) :
    ∃ t : T, orderOf t=2 ∧ t.val ∉ L := by
  obtain ⟨B,hBT,hdis,_,_,hcard⟩ := d.unitaryFour_sylow_complement h hH hp m hm hc
  have hB : B ≠ ⊥ := by
    intro hb
    have hi : L.relIndex (T : Subgroup G)=1 := by rw [←hcard,hb,card_bot]
    exact hST.ne (inf_eq_left.mpr (relIndex_eq_one.mp hi))
  let : Nontrivial B := B.nontrivial_iff_ne_bot.mpr hB
  obtain ⟨k,hk⟩ := (T.isPGroup'.to_le hBT).exists_card_eq
  have hkpos : 0<k := by
    have hh := Finite.one_lt_card (α := B)
    rw [hk] at hh
    by_contra hn
    have hz : k=0 := by omega
    simp [hz] at hh
  obtain ⟨b,hb⟩ := exists_prime_orderOf_dvd_card' (G := B) 2
    (hk ▸ dvd_pow_self 2 (by omega))
  refine ⟨⟨b.val,hBT b.property⟩,?_,?_⟩
  · exact (Subgroup.orderOf_coe ⟨b.val,hBT b.property⟩).symm.trans
      ((Subgroup.orderOf_coe b).trans hb)
  · intro hs
    have he := disjoint_def.mp hdis ⟨hBT b.property,hs⟩ b.property
    have he' : b=1 := Subtype.ext he
    rw [he',orderOf_one] at hb
    omega

open ChapterF.SourceCompletion.UnitaryNonbinary

omit d h hH hp hc in
/-- When the original T is inner, its image makes the same full extension's
outer index odd. No restriction on the parity of m is needed. -/
theorem UnitaryFourNormalizerMarking.outer_odd_of_inner_sylow
    (r : UnitaryFourNormalizerMarking L (residual H) ((T : Subgroup G) ⊓ L) m hm)
    (hs : (T : Subgroup G) ⊓ L = (T : Subgroup G)) :
    ¬ 2 ∣ (inner (ProjectiveGroup m hm)).relIndex r.extension.carrier := by
  let B := ChapterF.Source.parabolic ![L,residual H] ((T : Subgroup G) ⊓ L) 0 ⊓
    ChapterF.Source.parabolic ![L,residual H] ((T : Subgroup G) ⊓ L) 1
  let D := normalizer (L : Set G) ⊓ normalizer (residual H : Set G)
  have hTB : (T : Subgroup G) ≤ B := by
    rw [←hs]
    exact le_inf (le_sup_right.trans le_sup_left) (le_sup_right.trans le_sup_left)
  have hBD : B ≤ D := le_inf (inf_le_left.trans r.left_le) (inf_le_right.trans r.right_le)
  rw [r.outer_index_eq_source]
  intro hbad
  exact (T.subtype (hTB.trans hBD)).not_dvd_index
    (hbad.trans (index_dvd_of_le (show (T.subtype (hTB.trans hBD) : Subgroup D) ≤ B.subgroupOf D from
      fun x hx => hTB hx)))

/-- The inner-Sylow case discharges the ambient order premise for any one
specified full-normalizer extension, at every nonbinary parameter. -/
theorem Preparation.unitaryFour_order_of_inner_sylow
    (hs : (T : Subgroup G) ⊓ L = (T : Subgroup G))
    (r : UnitaryFourNormalizerMarking L (residual H) ((T : Subgroup G) ⊓ L) m hm) :
    Nat.card G = Nat.card r.extension.carrier :=
  d.unitaryFour_order_of_odd_outer h hH hp m hm hc r
    (UnitaryFourNormalizerMarking.outer_odd_of_inner_sylow m hm r hs)

/-- The original prepared U₄ branch either has its actual source extension,
order equality and recognition, or has the precise ambient fixed-root
obstruction. Outer existence is discharged in both comparison families. -/
theorem Preparation.unitaryFour_recognition_or_long_root_obstruction :
    1 < m ∧ n = 2*m ∧
    ((Nat.card G = Nat.card (d.unitaryFourNormalizerMarking h hH hp m hm hc).extension.carrier ∧
      ClassicalGroup.IsPSU G 4 (2^m)) ∨
    ∃ f : T, orderOf f=2 ∧ f.val ∉ L ∧ f.val ∉ residual H ∧
      (∀ i : Fin 2, Chapter1.IsSylowIn 2
        ((T : Subgroup G) ⊓ centralizer ({f.val} : Set G))
        (normalizer (![L,residual H] i : Set G) ⊓ centralizer ({f.val} : Set G))) ∧
      ∃ V : Subgroup G, IsPGroup 2 V ∧
        (T : Subgroup G) ⊓ centralizer ({f.val} : Set G) < V ∧
        V ≤ centralizer ({f.val} : Set G) ∧
        V ≤ normalizer (((T : Subgroup G) ⊓ centralizer ({f.val} : Set G) : Subgroup G) : Set G) ∧
        (∀ i : Fin 2, ¬ V ≤ normalizer (![L,residual H] i : Set G)) ∧
        (∀ B : Subgroup G, B ≤ (center (residual H)).map (residual H).subtype →
          V ≤ normalizer (B : Set G) → B=⊥) ∧
        let P := (T : Subgroup G) ⊓ centralizer ({f.val} : Set G)
        let Z := (center P ⊓ _root_.commutator P).map P.subtype
        let B := Z ⊓ (center (residual H)).map (residual H).subtype
        Z ≤ ((T : Subgroup G) ⊓ L) ⊓ centralizer ({f.val} : Set G) ∧
          V ≤ normalizer (Z : Set G) ∧
          (V ≤ normalizer (B : Set G) → B=⊥)) := by
  have hpar := d.unitary_reduced_native_comparison h hH.1.1.2 hp m hm hc
  refine ⟨hpar.1,hpar.2.1,?_⟩
  by_cases hs : (T : Subgroup G) ⊓ L = (T : Subgroup G)
  · exact Or.inl (d.unitaryFour_constructed_recognition h hH hp m hm hc
      (d.unitaryFour_order_of_inner_sylow h hH hp m hm hc hs _).le).2.2
  · exact Or.inr (d.unitaryFour_outer_long_root_obstruction h hH hp m hm hc
      (d.unitaryFour_exists_outer_involution h hH hp m hm hc (lt_of_le_of_ne inf_le_left hs)))

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
