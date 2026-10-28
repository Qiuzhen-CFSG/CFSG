module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.SmallerSelection
public import Theory.SpecificGroups.SymplecticFour.GeneratedRootMovement

/-!
# Root movement for both smaller-mover selectors

The natural quotient need only be surjective: if a subgroup centralizes
an original commutator, its quotient fixes every corresponding displacement.
A quadratic actor larger than q and two root groups cannot generate Sp₄
if it fixes the first root's displacement. This gives noncentralization
on the whole U-layer without splitting off its fixed kernel.

Apply this to the same two conjugates of the smaller join J supplied by
SmallerSelection. The chosen parabolic's quadratic action restricts to J;
the q² lower bound makes its quotient larger than q. Both conjugated
generating triples therefore move the full critical commutator. Generation,
full-Z fixed equality and the original parabolic position are retained.
The literal J ≤ Q₁ and field-sized image branches remain explicit.

The actual neighbor and path application is RootSelectedPaths. The large
proper-J and unequal-mover branches, the trapped root exclusion, and the
terminal distance exclusions are still needed for the final witness.
Source: MS93 (3.3), (5.6)--(5.7), printed pp.867,917--919.
-/

public noncomputable section
open Subgroup Representation Theory.GroupTheory Theory.SpecificGroups.SymplecticFour
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open scoped commutatorElement
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
open ChapterB.QuasisimpleSource MSCentralOrbit

private theorem quotient_displacement_fixed
    {G E : Type*} [Group G] [Field E]
    (S U A C : Subgroup G) (hn : S ≤ normalizer (U : Set G))
    (f : S →* Sp E) (π : U →* Multiplicative (Vector E))
    (hπ : Function.Surjective π)
    (hact : ∀ (s : S) (u : U),
      π ⟨s.val*u.val*s.val⁻¹,(mem_normalizer_iff.mp (hn s.property) u.val).mp u.property⟩ =
        Multiplicative.ofAdd (f s • (π u).toAdd))
    (hfix : ⁅A,U⁆ ≤ centralizer (C : Set G)) :
    displacementSpace ((A.subgroupOf S).map f) ≤
      TwoLocalCover.fixedSpace ((C.subgroupOf S).map f) := by
  apply Submodule.span_le.mpr
  rintro _ ⟨⟨y,v⟩,rfl⟩
  change y.val • v-v ∈ _
  obtain ⟨a,ha,he⟩ := y.property
  rw [←he]
  obtain ⟨u,hu⟩ := hπ (Multiplicative.ofAdd v)
  let ua : U := ⟨a.val*u.val*a.val⁻¹,
    (mem_normalizer_iff.mp (hn a.property) u.val).mp u.property⟩
  let w : U := ua * u⁻¹
  have hwval : w.val = ⁅a.val,u.val⁆ := rfl
  have hwπ : π w = Multiplicative.ofAdd (f a • v-v) := by
    change π (ua*u⁻¹) = _
    rw [map_mul,map_inv]
    have hh := hact a u
    change π ua = _ at hh
    rw [hh,hu]
    simp only [toAdd_ofAdd,ofAdd_sub,div_eq_mul_inv]
  have hwC : w.val ∈ centralizer (C : Set G) := by
    rw [hwval]
    exact hfix (commutator_mem_commutator ha u.property)
  rintro _ ⟨c,hc,rfl⟩
  have he : (⟨c.val*w.val*c.val⁻¹,
      (mem_normalizer_iff.mp (hn c.property) w.val).mp w.property⟩ : U) = w := by
    apply Subtype.ext
    exact mul_inv_eq_iff_eq_mul.mpr (hwC c.val hc)
  have hh := hact c w
  rw [he,hwπ] at hh
  exact (Multiplicative.ofAdd.injective hh).symm

variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

/-- Three-generator root movement on the whole natural cover, without a
splitting of its fixed kernel or a cubic-order restriction on the mover. -/
theorem Input.replacement_generated_root_not_centralized
    {geometry : Geometry d.radical} {a z : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : 4 ≤ geometry.b d.radical)
    (hsmall : (Q d.radical a).relIndex (Z d.radical z) < Nat.card F^2)
    (E : Subgroup (FreeAmalgam d.radical)) (hES : E ≤ stabilizer d.radical a)
    (hEc : Nat.card F < (Q d.radical a).relIndex E)
    (hEquad : ⁅⁅U d.radical a,E⁆,E⁆ = ⊥)
    (x : FreeAmalgam d.radical) (hx : x ∈ stabilizer d.radical a)
    (hgen : (E ⊔ Z d.radical z) ⊔
      (Z d.radical z).map (MulAut.conj x).toMonoidHom = stabilizer d.radical a) :
    ¬ ⁅Z d.radical z,U d.radical a⁆ ≤ centralizer (E : Set (FreeAmalgam d.radical)) := by
  intro hbad
  obtain ⟨B,hB,f,hf,hfQ,π,hπ,hπker,hact⟩ :=
    h.replacement_inner_natural_action d geometry hb path.start_color
  have hBF : Nat.card B.Carrier = Nat.card F := by rw [B.card_eq,hB,h.field_card]
  let S := stabilizer d.radical a
  let E₀ := E.subgroupOf S
  let A₀ := (Z d.radical z).subgroupOf S
  have hzS := path.endpoint_Z_le_start_stabilizer (by omega : 0 < geometry.b d.radical)
  let δ := f.comp (inclusion hzS)
  have hδ : δ.range = A₀.map f := by
    rw [MonoidHom.range_comp]
    congr 1
    ext y
    exact ⟨fun ⟨u,hu⟩ => hu ▸ u.property,fun hy => ⟨⟨y.val,hy⟩,rfl⟩⟩
  have hδc : Nat.card δ.range = (Q d.radical a).relIndex (Z d.radical z) :=
    Sp4Four.SourceComparison.quotient_image_card _ _ _ hzS f hfQ
  have hbpos : 0 < geometry.b d.radical := by omega
  let rev : CriticalPath d.radical geometry z a :=
    { start_color := path.end_color
      walk := path.walk.reverse
      shortest := by rw [SimpleGraph.Walk.length_reverse,path.shortest,SimpleGraph.dist_comm]
      critical := critical_reverse d.radical geometry
        (MSCentralOrbit.edgeCentralizerCondition d.radical (h.replacement_two_group d)
          (h.replacement_core_le d) (h.replacement_omegaOrbit_centralizer d))
        a path.start_color (by rw [geometry.distance_constant a path.start_color]; exact hbpos)
        z path.end_color path.critical }
  obtain ⟨_,hd,_⟩ := h.replacement_small_critical_root_image d hBF rev (by omega)
    π hπ δ hδc (fun y u => hact (inclusion hzS y) u) hsmall
  rw [hδ] at hd
  have hEquad' : ⁅E,U d.radical a⁆ ≤ centralizer (E : Set (FreeAmalgam d.radical)) := by
    rw [commutator_comm E]
    exact commutator_eq_bot_iff_le_centralizer.mp hEquad
  have hEfixed := quotient_displacement_fixed S (U d.radical a) E E (U_normalized a)
    f π hπ hact hEquad'
  have hAfixed := quotient_displacement_fixed S (U d.radical a) (Z d.radical z) E (U_normalized a)
    f π hπ hact hbad
  have hEq : ∀ y ∈ E₀.map f, ∀ w ∈ E₀.map f, ∀ v : Vector B.Carrier,
      y • (w • v-v)=w • v-v := by
    intro y hy w hw v
    exact hEfixed (Coinvariants.sub_mem_ker
      (ρ := (symplecticNatural 2).comp (E₀.map f).subtype) ⟨w,hw⟩ v) y hy
  have hEcard : Nat.card B.Carrier < Nat.card (E₀.map f) := by
    rw [←relIndex_ker]
    have hh := relIndex_map_map_of_injective f.ker E₀ S.subtype_injective
    rw [hfQ,map_subgroupOf_eq_of_le hES] at hh
    rw [←hh,hBF]
    exact hEc
  let xs : S := ⟨x,hx⟩
  have hgenS : (E₀ ⊔ A₀) ⊔ A₀.map (MulAut.conj xs).toMonoidHom = ⊤ := by
    apply map_injective S.subtype_injective
    rw [Subgroup.map_sup,Subgroup.map_sup,Subgroup.image_conjugate,
      map_subgroupOf_eq_of_le hES,map_subgroupOf_eq_of_le hzS,
      ←MonoidHom.range_eq_map,range_subtype]
    exact hgen
  have hmodel := congrArg (Subgroup.map f) hgenS
  rw [Subgroup.map_sup,Subgroup.map_sup,Subgroup.image_conjugate,
    map_top_of_surjective f hf] at hmodel
  apply generated_root_displacement_not_fixed (E₀.map f) (A₀.map f)
    ((A₀.map f).map (MulAut.conj (f xs)).toMonoidHom) hEq hEcard _ hmodel hAfixed
  rw [displacementSpace_conjugate,(toLinear (f xs)).finrank_map_eq,hd]


/-- In the literal parabolic branch the two selectors supplied by the
smaller join both move the full critical commutator. The same witnesses
retain generation, the full Z fixed subgroup, and parabolic placement. -/
theorem Input.replacement_smaller_mover_root_movement
    {geometry : Geometry d.radical} {a z t : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : 4 ≤ geometry.b d.radical)
    (hat : Adjacent d.radical a t) (hfirst : path.walk.getVert 1 = t)
    (hsmall : (Q d.radical a).relIndex (Z d.radical z) < Nat.card F^2)
    (B : BinaryField) (hB : B.degree = n)
    (f : stabilizer d.radical a →* Sp B.Carrier) (hf : Function.Surjective f)
    (hfQ : f.ker.map (stabilizer d.radical a).subtype = Q d.radical a)
    (hTf : ((Q d.radical t).subgroupOf (stabilizer d.radical a)).map f ≤ unipotent)
    (hindex : ∀ A : Subgroup (stabilizer d.radical a),
      (centralizer (A : Set (stabilizer d.radical a))).relIndex
        ((U d.radical a).subgroupOf (stabilizer d.radical a)) =
        2 ^ BinaryOffender.fixedCodim (restrictScalars (k := ZMod 2)
          (symplecticNatural (k := B.Carrier) 2)) (A.map f))
    (hquad : ⁅⁅(U d.radical a).subgroupOf (stabilizer d.radical a),
      ((CentralRootGeometry.wing (F := B.Carrier) true).map unipotent.subtype).comap f⁆,
      ((CentralRootGeometry.wing (F := B.Carrier) true).map unipotent.subtype).comap f⁆ = ⊥)
    (hJplane : (Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
      (Q d.radical t) (Nat.card F^2)).subgroupOf (stabilizer d.radical a) ≤
        ((CentralRootGeometry.wing (F := B.Carrier) true).map unipotent.subtype).comap f) :
    let D := (((CentralRootGeometry.wing (F := B.Carrier) true).map unipotent.subtype).comap f).map
      (stabilizer d.radical a).subtype
    let J := Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
      (Q d.radical t) (Nat.card F^2)
    ∃ g ∈ Ltilde d.radical a, ∃ x ∈ Ltilde d.radical a,
      let J₁ := J.map (MulAut.conj g).toMonoidHom
      let J₂ := J₁.map (MulAut.conj x⁻¹).toMonoidHom
      (J₁ ⊔ Z d.radical z) ⊔
        (Z d.radical z).map (MulAut.conj x).toMonoidHom = stabilizer d.radical a ∧
      (J₂ ⊔ Z d.radical z) ⊔
        (Z d.radical z).map (MulAut.conj x⁻¹).toMonoidHom = stabilizer d.radical a ∧
      ((Z d.radical a ⊓ centralizer (J₁ : Set (FreeAmalgam d.radical))) ⊓
        centralizer (J₂ : Set (FreeAmalgam d.radical)) =
          Z d.radical a ⊓ centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical))) ∧
      x ∈ normalizer (D : Set (FreeAmalgam d.radical)) ∧
      x ∈ (planeParabolic.comap f).map (stabilizer d.radical a).subtype ∧
      (¬ ⁅Z d.radical z,U d.radical a⁆ ≤ centralizer (J₁ : Set (FreeAmalgam d.radical))) ∧
      (¬ ⁅Z d.radical z,U d.radical a⁆ ≤ centralizer (J₂ : Set (FreeAmalgam d.radical))) := by
  dsimp only
  let S := stabilizer d.radical a
  let J := Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
    (Q d.radical t) (Nat.card F^2)
  let D := (((CentralRootGeometry.wing (F := B.Carrier) true).map unipotent.subtype).comap f).map S.subtype
  have hJS : J ≤ S := (Subgroup.SmallMover.join_le _ _ _ _).trans
    (fun _ hx => hx.2 a (adjacent_symm d.radical hat))
  have hJD : J ≤ D := by
    have hh := map_mono (f := S.subtype) hJplane
    rwa [map_subgroupOf_eq_of_le hJS] at hh
  have hDq : ⁅⁅U d.radical a,D⁆,D⁆ = ⊥ := by
    have hh := congrArg (Subgroup.map S.subtype) hquad
    rwa [map_commutator,map_commutator,
      map_subgroupOf_eq_of_le ((U_le_Z a).trans (Z_le_stabilizer d.radical a)),Subgroup.map_bot] at hh
  have hJq : ⁅⁅U d.radical a,J⁆,J⁆ = ⊥ := le_bot_iff.mp
    ((commutator_mono (commutator_mono le_rfl hJD) hJD).trans_eq hDq)
  have hJc : Nat.card F < (Q d.radical a).relIndex J := by
    have hi := h.replacement_small_mover_join_index d geometry hb path.start_color hat
    have hq : 1 < Nat.card F := Finite.one_lt_card
    have hlt : Nat.card F < Nat.card F^2 := by nlinarith
    exact hlt.trans_le hi
  obtain ⟨g,hg,x,hx,hgen,hpair,hfixed,hxn,hxp⟩ :=
    h.replacement_smaller_mover_root_selection d path hb hat hfirst hsmall
      B hB f hf hfQ hTf hindex hJplane
  have hgS := Ltilde_le_stabilizer a hg
  have hxS := Ltilde_le_stabilizer a hx
  have transport (E : Subgroup (FreeAmalgam d.radical))
      (hES : E ≤ S) (hEc : Nat.card F < (Q d.radical a).relIndex E)
      (hEq : ⁅⁅U d.radical a,E⁆,E⁆ = ⊥)
      (y : FreeAmalgam d.radical) (hy : y ∈ S) :
      E.map (MulAut.conj y).toMonoidHom ≤ S ∧
      Nat.card F < (Q d.radical a).relIndex (E.map (MulAut.conj y).toMonoidHom) ∧
      ⁅⁅U d.radical a,E.map (MulAut.conj y).toMonoidHom⁆,
        E.map (MulAut.conj y).toMonoidHom⁆ = ⊥ := by
    have hS : S.map (MulAut.conj y).toMonoidHom = S :=
      mem_normalizer_iff_map_conj_eq.mp (S.le_normalizer hy)
    have hU : (U d.radical a).map (MulAut.conj y).toMonoidHom = U d.radical a :=
      mem_normalizer_iff_map_conj_eq.mp (U_normalized a hy)
    have hQ : (Q d.radical a).map (MulAut.conj y).toMonoidHom = Q d.radical a :=
      mem_normalizer_iff_map_conj_eq.mp (Q_normalized d.radical a hy)
    refine ⟨hS ▸ map_mono hES,?_,?_⟩
    · conv_rhs => rw [←hQ]
      rwa [relIndex_map_map_of_injective _ _ (MulAut.conj y).injective]
    · have hh := congrArg (Subgroup.map (MulAut.conj y).toMonoidHom) hEq
      rwa [map_commutator,map_commutator,hU,Subgroup.map_bot] at hh
  obtain ⟨hJ₁S,hJ₁c,hJ₁q⟩ := transport J hJS hJc hJq g hgS
  obtain ⟨hJ₂S,hJ₂c,hJ₂q⟩ := transport _ hJ₁S hJ₁c hJ₁q x⁻¹ (S.inv_mem hxS)
  have hgen₂ : ((J.map (MulAut.conj g).toMonoidHom).map (MulAut.conj x⁻¹).toMonoidHom ⊔
      Z d.radical z) ⊔ (Z d.radical z).map (MulAut.conj x⁻¹).toMonoidHom = S := by
    have hh := congrArg (Subgroup.map (MulAut.conj x⁻¹).toMonoidHom) hgen
    have hS : S.map (MulAut.conj x⁻¹).toMonoidHom = S :=
      mem_normalizer_iff_map_conj_eq.mp (S.le_normalizer (S.inv_mem hxS))
    have hcomp : (MulAut.conj x⁻¹).toMonoidHom.comp (MulAut.conj x).toMonoidHom =
        MonoidHom.id (FreeAmalgam d.radical) := by
      apply MonoidHom.ext
      intro y
      change x⁻¹*(x*y*x⁻¹)*(x⁻¹)⁻¹ = y
      group
    have hz : ((Z d.radical z).map (MulAut.conj x).toMonoidHom).map
        (MulAut.conj x⁻¹).toMonoidHom = Z d.radical z := by
      rw [Subgroup.map_map,hcomp,Subgroup.map_id]
    rw [Subgroup.map_sup,Subgroup.map_sup,hz,hS] at hh
    rw [sup_assoc,sup_comm (Z d.radical z),←sup_assoc]
    exact hh
  exact ⟨g,hg,x,hx,hgen,hgen₂,hfixed,hxn,hxp,
    h.replacement_generated_root_not_centralized d path hb hsmall _ hJ₁S hJ₁c hJ₁q x hxS hgen,
    h.replacement_generated_root_not_centralized d path hb hsmall _ hJ₂S hJ₂c hJ₂q x⁻¹
      (S.inv_mem hxS) hgen₂⟩

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
