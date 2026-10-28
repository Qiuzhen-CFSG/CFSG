module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.CubicSelection
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.UnequalMovers

/-!
# The full parabolic fixed-layer selector

In the reciprocal field-sized critical-image branch, the endpoint lies
in the chosen parabolic's actual two-core Q₁. Its full preimage has order
q³ modulo Q-alpha and the exact natural fixed index q². Applying the
checked full-plane selector to this Q₁ gives a generating pair of its
conjugates. Their common fixed subgroup on the whole Z-layer is exactly
the ambient-fixed part, and the same selector lies in the original
chosen parabolic.

This proves MS93 (5.6)(b,d), printed pp.917--918, in the root branch
without requiring the small-mover join to be cubic. The actual maximizing
parabolic application also retains the separation test from (5.5).
Generation using the smaller join in (5.6)(c), larger critical images,
selected paths, terminal exclusions and the distance-two witness remain
unproved. Every central attachment and the original field degree remain.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Representation.OneCohomology
open Theory.GroupTheory Theory.SpecificGroups.SymplecticFour
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
open ChapterB.QuasisimpleSource MSCentralOrbit
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

/-- The full parabolic fixed-layer and positioning clauses in the root
branch of MS93 (5.6), without requiring the small-mover join to be cubic. -/
theorem Input.replacement_parabolic_root_fixed_selection
    {geometry : Geometry d.radical} {a z t : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : 4 ≤ geometry.b d.radical)
    (hfirst : path.walk.getVert 1 = t)
    (hsmall : (Q d.radical a).relIndex (Z d.radical z) < Nat.card F^2)
    (B : BinaryField) (hB : B.degree = n)
    (f : stabilizer d.radical a →* Sp B.Carrier) (hf : Function.Surjective f)
    (hfQ : f.ker.map (stabilizer d.radical a).subtype = Q d.radical a)
    (hTf : ((Q d.radical t).subgroupOf (stabilizer d.radical a)).map f ≤ unipotent)
    (hindex : ∀ A : Subgroup (stabilizer d.radical a),
      (centralizer (A : Set (stabilizer d.radical a))).relIndex
        ((U d.radical a).subgroupOf (stabilizer d.radical a)) =
        2 ^ fixedCodim (restrictScalars (k := ZMod 2)
          (symplecticNatural (k := B.Carrier) 2)) (A.map f))
    (hcore : (planeParabolic.comap f).pCoreIn 2 =
      ((CentralRootGeometry.wing (F := B.Carrier) true).map unipotent.subtype).comap f) :
    let D := (((CentralRootGeometry.wing (F := B.Carrier) true).map unipotent.subtype).comap f).map
      (stabilizer d.radical a).subtype
    ∃ g ∈ Ltilde d.radical a, ∃ x ∈ Ltilde d.radical a,
      (D.map (MulAut.conj g).toMonoidHom ⊔ Z d.radical z) ⊔
        (Z d.radical z).map (MulAut.conj x).toMonoidHom = stabilizer d.radical a ∧
      ((Z d.radical a ⊓ centralizer (D.map (MulAut.conj g).toMonoidHom : Set (FreeAmalgam d.radical))) ⊓
        centralizer ((D.map (MulAut.conj g).toMonoidHom).map
          (MulAut.conj x⁻¹).toMonoidHom : Set (FreeAmalgam d.radical)) =
          Z d.radical a ⊓ centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical))) ∧
      x ∈ normalizer (D : Set (FreeAmalgam d.radical)) ∧
      x ∈ (planeParabolic.comap f).map (stabilizer d.radical a).subtype := by
  dsimp only
  let S := stabilizer d.radical a
  let P := (CentralRootGeometry.wing (F := B.Carrier) true).map unipotent.subtype
  let D₀ := P.comap f
  let D := D₀.map S.subtype
  have hDS : D ≤ S := (map_le_range _ _).trans_eq (range_subtype _)
  have hsub : D.subgroupOf S = D₀ := comap_map_eq_self_of_injective S.subtype_injective _
  have hm : D₀.map f = P := map_comap_eq_self_of_surjective hf _
  have hcard : Nat.card B.Carrier = Nat.card F := by rw [B.card_eq,hB,h.field_card]
  have hk : f.ker ≤ D₀ := by
    intro x hx
    change f x ∈ P
    rw [MonoidHom.mem_ker.mp hx]
    exact P.one_mem
  have hQD : Q d.radical a ≤ D := by
    rw [←hfQ]
    exact map_mono hk
  have hpD : IsPGroup 2 D := by
    have hh : IsPGroup 2 D₀ := by
      change IsPGroup 2 (P.comap f)
      rw [←hcore]
      exact isPGroup_pCoreIn 2 (planeParabolic.comap f)
    exact hh.map S.subtype
  have hDc : (Q d.radical a).relIndex D = Nat.card F^3 := by
    rw [←hfQ]
    rw [relIndex_map_map_of_injective f.ker D₀ S.subtype_injective,relIndex_ker,hm,
      card_map_of_injective unipotent.subtype_injective,CentralRootGeometry.card_wing,hcard]
  have hDm : (centralizer (D : Set (FreeAmalgam d.radical))).relIndex
      (U d.radical a) ≤ Nat.card F^2 := by
    have hh := Subgroup.SmallMover.centralizer_index_map S.subtype S.subtype_injective
      ((U d.radical a).subgroupOf S) D₀
    rw [map_subgroupOf_eq_of_le ((U_le_Z a).trans (Z_le_stabilizer d.radical a)),hindex,hm] at hh
    have hp : P=SymplecticConjugatePair.planeRadical :=
      SymplecticConjugatePair.planeRadical_eq_wing.symm
    rw [hp] at hh
    change (centralizer (D : Set (FreeAmalgam d.radical))).relIndex (U d.radical a) =
      2 ^ fixedCodim (SymplecticConjugatePair.binaryNatural (F := B.Carrier))
        SymplecticConjugatePair.planeRadical at hh
    rw [SymplecticConjugatePair.planeRadical_natural_fixedCodim B.card_eq] at hh
    rw [hh,h.field_card,hB,show 2*n=n*2 by omega,pow_mul]
  have hpos : 0 < geometry.b d.radical := by omega
  let rev : CriticalPath d.radical geometry z a :=
    { start_color := path.end_color
      walk := path.walk.reverse
      shortest := by rw [SimpleGraph.Walk.length_reverse,path.shortest,SimpleGraph.dist_comm]
      critical := critical_reverse d.radical geometry
        (MSCentralOrbit.edgeCentralizerCondition d.radical (h.replacement_two_group d)
          (h.replacement_core_le d) (h.replacement_omegaOrbit_centralizer d))
        a path.start_color (by rwa [geometry.distance_constant a path.start_color])
        z path.end_color path.critical }
  have hi := h.replacement_small_critical_indices_eq_field d rev hpos hsmall
  have hzT : Z d.radical z ≤ Q d.radical t := by
    rw [←hfirst]
    apply Z_le_Q_of_dist_lt d.radical z (geometry.exists_critical z path.end_color)
    rw [SimpleGraph.dist_comm,path.dist_end,geometry.distance_constant z path.end_color]
    change path.walk.length - 1 < geometry.b d.radical
    rw [path.length_eq_b]
    omega
  have hzS := path.endpoint_Z_le_start_stabilizer hpos
  have haS := rev.endpoint_Z_le_start_stabilizer hpos
  have hC : C d.radical z = Q d.radical z := MSCentralOrbit.C_eq_Q _
    (h.replacement_two_group d) (h.replacement_core_le d)
    (h.replacement_omegaOrbit_centralizer d) z path.end_color
  have hcz : (centralizer (Z d.radical z : Set (FreeAmalgam d.radical))).relIndex (Z d.radical a) =
      (Q d.radical z).relIndex (Z d.radical a) := by
    rw [←hC]
    change ((centralizer (Z d.radical z : Set (FreeAmalgam d.radical))).subgroupOf (Z d.radical a)).index =
      ((stabilizer d.radical z ⊓ centralizer (Z d.radical z : Set (FreeAmalgam d.radical))).subgroupOf
        (Z d.radical a)).index
    congr 1
    ext x
    exact ⟨fun hx => ⟨haS x.property,hx⟩,fun hx => hx.2⟩
  let := finite_Z d.radical a
  have hiU : (centralizer (Z d.radical z : Set (FreeAmalgam d.radical))).relIndex
      (U d.radical a) ≤ Nat.card B.Carrier := by
    apply (relIndex_le_of_le_right (U_le_Z a) index_ne_zero_of_finite).trans
    rw [hcz,hi.2,hcard]
  let A₀ := (Z d.radical z).subgroupOf S
  let A₁ := (A₀.map f).subgroupOf unipotent
  have hAU : A₀.map f ≤ unipotent := (map_mono (comap_mono hzT)).trans hTf
  have hAm : A₁.map unipotent.subtype = A₀.map f := map_subgroupOf_eq_of_le hAU
  have hiA : CentralRootGeometry.SmallMovers.movingIndex A₁ ≤ Nat.card B.Carrier := by
    have hi₀ := Subgroup.SmallMover.centralizer_index_map S.subtype S.subtype_injective
      ((U d.radical a).subgroupOf S) A₀
    rw [map_subgroupOf_eq_of_le ((U_le_Z a).trans (Z_le_stabilizer d.radical a)),
      map_subgroupOf_eq_of_le hzS,hindex] at hi₀
    rw [hi₀] at hiU
    rw [←CentralRootGeometry.SmallMovers.binary_movingIndex]
    change 2 ^ fixedCodim ((restrictScalars (k := ZMod 2)
      (symplecticNatural (k := B.Carrier) 2)).comp unipotent.subtype) A₁ ≤ _
    rw [fixedCodim,fixedSpace_comp_map,hAm]
    exact hiU
  have hAw : A₁ ≤ CentralRootGeometry.wing true := by
    by_contra hn
    have hq : 1 < Nat.card B.Carrier := Finite.one_lt_card
    have hq2 : Nat.card B.Carrier < Nat.card B.Carrier^2 := by nlinarith
    have he := CentralRootGeometry.SmallMovers.Degree.movingIndex_eq_square_of_not_le_wing A₁
      (hiA.trans hq2.le) hn
    omega
  have hAz : A₀.map f ≤ P := by
    rw [←hAm]
    exact map_mono hAw
  have hzD : Z d.radical z ≤ D := by
    have hh : A₀ ≤ D₀ := (map_le_iff_le_comap).mp hAz
    have hh' := map_mono (f := S.subtype) hh
    rwa [map_subgroupOf_eq_of_le hzS] at hh'
  obtain ⟨g,hg,x,hx,hgen,hpair,hposition⟩ :=
    h.replacement_cubic_mover_root_selection d path hb hsmall D hDS hQD hpD hDc hDm
  have hxN := hposition hzD
  have hxS : x ∈ S := Ltilde_le_stabilizer a hx
  have hxN₀ : (⟨x,hxS⟩ : S) ∈ normalizer (D₀ : Set S) := by
    rw [←hsub]
    apply mem_normalizer_iff.mpr
    intro y
    change y.val ∈ D ↔ x*y.val*x⁻¹ ∈ D
    exact mem_normalizer_iff.mp hxN y.val
  have hxP := D₀.le_normalizer_map f (mem_map_of_mem f hxN₀)
  rw [hm] at hxP
  have hPrad : P=planeRadicalAmbient := SymplecticConjugatePair.planeRadical_eq_wing.symm
  rw [hPrad,planeRadicalAmbient_normalizer B.card_eq (by rw [hB]; exact h.nonbinary)] at hxP
  refine ⟨g,hg,x,hx,hgen,?_,hxN,⟨⟨x,hxS⟩,hxP,rfl⟩⟩
  have hfixed : centralizer (D.map (MulAut.conj g).toMonoidHom : Set (FreeAmalgam d.radical)) ⊓
      centralizer ((D.map (MulAut.conj g).toMonoidHom).map
        (MulAut.conj x⁻¹).toMonoidHom : Set (FreeAmalgam d.radical)) =
      centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical)) := by
    apply le_antisymm
    · intro w hw s hs
      have h₁ : D.map (MulAut.conj g).toMonoidHom ≤ centralizer ({w} : Set (FreeAmalgam d.radical)) :=
        fun y hy => mem_centralizer_singleton_iff.mpr (hw.1 y hy)
      have h₂ : (D.map (MulAut.conj g).toMonoidHom).map (MulAut.conj x⁻¹).toMonoidHom ≤
          centralizer ({w} : Set (FreeAmalgam d.radical)) :=
        fun y hy => mem_centralizer_singleton_iff.mpr (hw.2 y hy)
      exact mem_centralizer_singleton_iff.mp ((sup_le h₁ h₂) (hpair.symm ▸ hs))
    · exact le_inf (centralizer_le (show D.map (MulAut.conj g).toMonoidHom ≤ stabilizer d.radical a from
        le_sup_left.trans_eq hpair))
        (centralizer_le (show (D.map (MulAut.conj g).toMonoidHom).map (MulAut.conj x⁻¹).toMonoidHom ≤
          stabilizer d.radical a from le_sup_right.trans_eq hpair))
  rw [inf_assoc,hfixed]

/-- One actual maximizing parabolic supplies the (5.5) separation test and
the (5.6)(b,d) root-branch selector. All degree, kernel, core and maximality
premises of the fixed-layer helper are discharged by the original input. -/
theorem Input.replacement_maximizing_parabolic_root_fixed_selection
    {geometry : Geometry d.radical} {a z t : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : 4 ≤ geometry.b d.radical)
    (hat : Adjacent d.radical a t) (hfirst : path.walk.getVert 1 = t)
    (hsmall : (Q d.radical a).relIndex (Z d.radical z) < Nat.card F^2) :
    ∃ B : BinaryField, B.degree = n ∧
      ∃ f : stabilizer d.radical a →* Sp B.Carrier,
        Function.Surjective f ∧ f.ker.map (stabilizer d.radical a).subtype = Q d.radical a ∧
        ((Q d.radical t).subgroupOf (stabilizer d.radical a)).map f ≤ unipotent ∧
        (∀ A : Subgroup (stabilizer d.radical a),
          (centralizer (A : Set (stabilizer d.radical a))).relIndex
            ((U d.radical a).subgroupOf (stabilizer d.radical a)) =
            2 ^ fixedCodim (restrictScalars (k := ZMod 2)
              (symplecticNatural (k := B.Carrier) 2)) (A.map f)) ∧
        (let P := (CentralRootGeometry.wing (F := B.Carrier) true).map unipotent.subtype
         let Q₁ := P.comap f
         let D := Q₁.map (stabilizer d.radical a).subtype
         let J := Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
           (Q d.radical t) (Nat.card F^2)
         (planeParabolic.comap f).pCoreIn 2 = Q₁ ∧
         (Q d.radical t).subgroupOf (stabilizer d.radical a) ≤ planeParabolic.comap f ∧
         ⁅⁅(U d.radical a).subgroupOf (stabilizer d.radical a),Q₁⁆,Q₁⁆ = ⊥ ∧
         (∀ x : Sp B.Carrier,
           Nat.card (J.subgroupOf (stabilizer d.radical a) ⊓
             (P.map (MulAut.conj x).toMonoidHom).comap f :
               Subgroup (stabilizer d.radical a)) ≤ Nat.card
                 (J.subgroupOf (stabilizer d.radical a) ⊓ Q₁ :
                   Subgroup (stabilizer d.radical a))) ∧
         (∀ c : Vertex d.radical, Adjacent d.radical c t →
           let Jc := Subgroup.SmallMover.join (U d.radical c) (Q d.radical c)
             (Q d.radical t) (Nat.card F^2)
           (Jc ≠ J ∨ ¬ J.subgroupOf (stabilizer d.radical a) ≤ Q₁) →
           Nat.card F^2 < (centralizer ((J ⊔ Jc : Subgroup (FreeAmalgam d.radical)) :
             Set (FreeAmalgam d.radical))).relIndex (U d.radical a) ∧
           ¬ IsQuadratic (restrictScalars (k := ZMod 2)
             (symplecticNatural (k := B.Carrier) 2))
             (((J ⊔ Jc).subgroupOf (stabilizer d.radical a)).map f)) ∧
         ∃ g ∈ Ltilde d.radical a, ∃ x ∈ Ltilde d.radical a,
           (D.map (MulAut.conj g).toMonoidHom ⊔ Z d.radical z) ⊔
             (Z d.radical z).map (MulAut.conj x).toMonoidHom = stabilizer d.radical a ∧
           ((Z d.radical a ⊓ centralizer (D.map (MulAut.conj g).toMonoidHom : Set (FreeAmalgam d.radical))) ⊓
             centralizer ((D.map (MulAut.conj g).toMonoidHom).map
               (MulAut.conj x⁻¹).toMonoidHom : Set (FreeAmalgam d.radical)) =
               Z d.radical a ⊓ centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical))) ∧
           x ∈ normalizer (D : Set (FreeAmalgam d.radical)) ∧
           x ∈ (planeParabolic.comap f).map (stabilizer d.radical a).subtype) := by
  obtain ⟨B,hB,f,hf,hfQ,hTf,hindex,hcore,hTP,hquad,hmax,hseparation⟩ :=
    h.replacement_maximizing_parabolic_separation d geometry hb path.start_color hat
  refine ⟨B,hB,f,hf,hfQ,hTf,hindex,hcore,hTP,hquad,hmax,hseparation,?_⟩
  exact h.replacement_parabolic_root_fixed_selection d path hb hfirst hsmall
    B hB f hf hfQ hTf hindex hcore

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
