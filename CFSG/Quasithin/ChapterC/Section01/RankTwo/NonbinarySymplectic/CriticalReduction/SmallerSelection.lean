module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.ParabolicMover
public import Theory.SpecificGroups.SymplecticFour.SmallPlaneGeneration
/-!
# Generation by the smaller mover in the root-image branch

The original endpoint is a full long root under the very same maximizing
parabolic marking: reciprocal critical indices and the full U fixed-index
formula give its order and displacement line. The smaller join contains
that root and has image order at least q squared. The arbitrary-degree
plane-actor selector therefore generates using J itself.

Both conjugators lift into the original residual through the whole Q-kernel.
Their full plane radicals generate, and the already proved equality of the
J- and Q₁-fixed subgroups transports this to the whole Z-layer. The selector
belongs to the original parabolic. The final application retains the actual
maximizing parabolic, endpoint placement and separation clause, supplying
all three conclusions for the same pair in the literal J ≤ Q₁ branch.

Source: MS93 (5.6)(b--d), printed pp.917--918, field-sized critical-image
branch. Larger images, unequal-mover selection, selected paths, terminal
exclusions and the minimum-replacement distance-two witness remain open.
No original-radical characteristic control is inferred from these results.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Representation.OneCohomology
open Theory.GroupTheory Theory.SpecificGroups.SymplecticFour
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
open ChapterB.QuasisimpleSource MSCentralOrbit
private theorem full_of_full_image {S T : Type*} [Group S] [Group T]
    (f : S →* T) (D : Subgroup S) (hk : f.ker ≤ D) (hm : D.map f = ⊤) : D=⊤ := by
  apply top_unique
  intro y _
  obtain ⟨z,hz,he⟩ := (show f y ∈ D.map f by rw [hm]; trivial)
  have hzy : z⁻¹*y ∈ f.ker := by
    change f (z⁻¹*y)=1
    simp [he]
  have hh := D.mul_mem hz (hk hzy)
  simpa using hh

private theorem kernel_le_conjugate {S T : Type*} [Group S] [Group T]
    (f : S →* T) (D : Subgroup S) (hk : f.ker ≤ D) (g : S) :
    f.ker ≤ D.map (MulAut.conj g).toMonoidHom := by
  intro y hy
  refine ⟨g⁻¹*y*g,hk ?_,?_⟩
  · change f (g⁻¹*y*g)=1
    simp [show f y=1 from hy]
  · simp [MulAut.conj_apply,mul_assoc]

private theorem conjugate_fixed_eq {G : Type*} [Group G]
    (Z J D : Subgroup G) (he : Z ⊓ centralizer (J : Set G) = Z ⊓ centralizer (D : Set G))
    (g : G) (hg : g ∈ normalizer (Z : Set G)) :
    Z ⊓ centralizer (J.map (MulAut.conj g).toMonoidHom : Set G) =
      Z ⊓ centralizer (D.map (MulAut.conj g).toMonoidHom : Set G) := by
  have hz := mem_normalizer_iff_map_conj_eq.mp hg
  change Z.map (MulAut.conj g).toMonoidHom = Z at hz
  have hh := congrArg (Subgroup.map (MulAut.conj g).toMonoidHom) he
  rw [map_inf _ _ _ (MulAut.conj g).injective,map_inf _ _ _ (MulAut.conj g).injective,
    Theory.GroupTheory.map_centralizer_equiv,Theory.GroupTheory.map_centralizer_equiv,
    hz] at hh
  exact hh

private theorem fixed_pair_of_generation {G : Type*} [Group G]
    (Z E A S : Subgroup G) (hgen : E ⊔ A = S) :
    (Z ⊓ centralizer (E : Set G)) ⊓ centralizer (A : Set G) =
      Z ⊓ centralizer (S : Set G) := by
  apply le_antisymm
  · intro w hw
    refine ⟨hw.1.1,?_⟩
    have hE : E ≤ centralizer ({w} : Set G) :=
      fun y hy => mem_centralizer_singleton_iff.mpr (hw.1.2 y hy)
    have hA : A ≤ centralizer ({w} : Set G) :=
      fun y hy => mem_centralizer_singleton_iff.mpr (hw.2 y hy)
    intro y hy
    exact mem_centralizer_singleton_iff.mp ((sup_le hE hA) (hgen.symm ▸ hy))
  · exact fun w hw => ⟨⟨hw.1,centralizer_le (show E ≤ S from le_sup_left.trans_eq hgen) hw.2⟩,
      centralizer_le (show A ≤ S from le_sup_right.trans_eq hgen) hw.2⟩

variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

private theorem root_image_from_indices
    {geometry : Geometry d.radical} {a z : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : 4 ≤ geometry.b d.radical)
    (hsmall : (Q d.radical a).relIndex (Z d.radical z) < Nat.card F^2)
    (B : BinaryField) (hB : B.degree = n)
    (f : stabilizer d.radical a →* Sp B.Carrier)
    (hfQ : f.ker.map (stabilizer d.radical a).subtype = Q d.radical a)
    (hindex : ∀ A : Subgroup (stabilizer d.radical a),
      (centralizer (A : Set (stabilizer d.radical a))).relIndex
        ((U d.radical a).subgroupOf (stabilizer d.radical a)) =
        2 ^ fixedCodim (restrictScalars (k := ZMod 2)
          (symplecticNatural (k := B.Carrier) 2)) (A.map f)) :
    let A := ((Z d.radical z).subgroupOf (stabilizer d.radical a)).map f
    Nat.card A = Nat.card B.Carrier ∧ Module.finrank B.Carrier (displacementSpace A) = 1 := by
  dsimp only
  let S := stabilizer d.radical a
  let A₀ := (Z d.radical z).subgroupOf S
  let A := A₀.map f
  have hBF : Nat.card B.Carrier = Nat.card F := by rw [B.card_eq,hB,h.field_card]
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
  have hzS := path.endpoint_Z_le_start_stabilizer hpos
  have haS := rev.endpoint_Z_le_start_stabilizer hpos
  have hc : Nat.card A = Nat.card B.Carrier := by
    rw [←relIndex_ker]
    have hh := relIndex_map_map_of_injective f.ker A₀ S.subtype_injective
    rw [hfQ,map_subgroupOf_eq_of_le hzS] at hh
    rw [←hh,hi.1,hBF]
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
    rw [hcz,hi.2,hBF]
  have hh := Subgroup.SmallMover.centralizer_index_map S.subtype S.subtype_injective
    ((U d.radical a).subgroupOf S) A₀
  rw [map_subgroupOf_eq_of_le ((U_le_Z a).trans (Z_le_stabilizer d.radical a)),
    map_subgroupOf_eq_of_le hzS,hindex] at hh
  rw [hh] at hiU
  let σ := restrictScalars (k := ZMod 2) (symplecticNatural (k := B.Carrier) 2)
  have hquot : 2 ^ fixedCodim σ A = Nat.card (Vector B.Carrier ⧸ TwoLocalCover.fixedSpace A) := by
    let C := TwoLocalCover.fixedSpace A
    have he : fixedSpace σ A = C.restrictScalars (ZMod 2) := by
      ext v
      exact ⟨fun hv x hx => hv ⟨x,hx⟩,fun hv x => hv x.val x.property⟩
    change 2 ^ Module.finrank (ZMod 2) (Vector B.Carrier ⧸ fixedSpace σ A) = _
    rw [he]
    have hh := Nat.card_congr (Submodule.Quotient.restrictScalarsEquiv (ZMod 2) C).toEquiv
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod] at hh
    exact hh
  change 2 ^ fixedCodim σ A ≤ Nat.card B.Carrier at hiU
  rw [hquot,fixed_quotient_card] at hiU
  have hq : 1 < Nat.card B.Carrier := Finite.one_lt_card
  have hdle : Module.finrank B.Carrier (displacementSpace A) ≤ 1 := by
    by_contra hn
    have hpow := Nat.pow_le_pow_right (by omega : 1 ≤ Nat.card B.Carrier)
      (show 2 ≤ Module.finrank B.Carrier (displacementSpace A) by omega)
    nlinarith
  have hdne : Module.finrank B.Carrier (displacementSpace A) ≠ 0 := by
    intro hz
    have hh := card_actor_le_displacement_dimension A
    rw [hz,hc] at hh
    norm_num at hh
    omega
  refine ⟨hc,?_⟩
  change Module.finrank B.Carrier (displacementSpace A) = 1
  omega


/-- The existing root-image calculation in any exact natural-index marking.
This exposes the same field-sized image and displacement line for the
point-radical selector, without choosing a new quotient or dropping its kernel. -/
theorem Input.replacement_small_critical_image_dimensions
    {geometry : Geometry d.radical} {a z : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : 4 ≤ geometry.b d.radical)
    (hsmall : (Q d.radical a).relIndex (Z d.radical z) < Nat.card F^2)
    (B : BinaryField) (hB : B.degree = n)
    (f : stabilizer d.radical a →* Sp B.Carrier)
    (hfQ : f.ker.map (stabilizer d.radical a).subtype = Q d.radical a)
    (hindex : ∀ A : Subgroup (stabilizer d.radical a),
      (centralizer (A : Set (stabilizer d.radical a))).relIndex
        ((U d.radical a).subgroupOf (stabilizer d.radical a)) =
        2 ^ fixedCodim (restrictScalars (k := ZMod 2)
          (symplecticNatural (k := B.Carrier) 2)) (A.map f)) :
    let A := ((Z d.radical z).subgroupOf (stabilizer d.radical a)).map f
    Nat.card A = Nat.card B.Carrier ∧ Module.finrank B.Carrier (displacementSpace A) = 1 := by
  exact root_image_from_indices h d path hb hsmall B hB f hfQ hindex

/-- In the literal chosen-parabolic branch, generation uses the entire
smaller-mover join J. The same two residual elements give the full Z fixed
subgroup and the original parabolic positioning. -/
theorem Input.replacement_smaller_mover_root_selection
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
        2 ^ fixedCodim (restrictScalars (k := ZMod 2)
          (symplecticNatural (k := B.Carrier) 2)) (A.map f))
    (hJplane : (Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
      (Q d.radical t) (Nat.card F^2)).subgroupOf (stabilizer d.radical a) ≤
        ((CentralRootGeometry.wing (F := B.Carrier) true).map unipotent.subtype).comap f) :
    let D := (((CentralRootGeometry.wing (F := B.Carrier) true).map unipotent.subtype).comap f).map
      (stabilizer d.radical a).subtype
    let J := Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
      (Q d.radical t) (Nat.card F^2)
    ∃ g ∈ Ltilde d.radical a, ∃ x ∈ Ltilde d.radical a,
      (J.map (MulAut.conj g).toMonoidHom ⊔ Z d.radical z) ⊔
        (Z d.radical z).map (MulAut.conj x).toMonoidHom = stabilizer d.radical a ∧
      (D.map (MulAut.conj g).toMonoidHom ⊔
        (D.map (MulAut.conj g).toMonoidHom).map (MulAut.conj x⁻¹).toMonoidHom = stabilizer d.radical a) ∧
      ((Z d.radical a ⊓ centralizer (J.map (MulAut.conj g).toMonoidHom : Set (FreeAmalgam d.radical))) ⊓
        centralizer ((J.map (MulAut.conj g).toMonoidHom).map
          (MulAut.conj x⁻¹).toMonoidHom : Set (FreeAmalgam d.radical)) =
          Z d.radical a ⊓ centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical))) ∧
      x ∈ normalizer (D : Set (FreeAmalgam d.radical)) ∧
      x ∈ (planeParabolic.comap f).map (stabilizer d.radical a).subtype := by
  dsimp only
  let S := stabilizer d.radical a
  let P := (CentralRootGeometry.wing (F := B.Carrier) true).map unipotent.subtype
  let D₀ := P.comap f
  let D := D₀.map S.subtype
  let J := Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
    (Q d.radical t) (Nat.card F^2)
  let J₀ := J.subgroupOf S
  let A₀ := (Z d.radical z).subgroupOf S
  let L₀ := (Ltilde d.radical a).subgroupOf S
  let := finite_stabilizer d.radical a
  have hsat := h.replacement_small_mover_parabolic_intersection d geometry hb path.start_color hat
    B hB f hf hindex hJplane
  change Q d.radical t ⊓ D = J at hsat
  have hzJ := h.replacement_root_endpoint_le_small_mover d path hb hat hfirst hsmall
    B hB f hf hTf hindex hJplane
  have hJD : J ≤ D := by rw [←hsat]; exact inf_le_right
  have hDS : D ≤ S := (map_le_range _ _).trans_eq (range_subtype _)
  have hJS : J ≤ S := hJD.trans hDS
  have hzS := hzJ.trans hJS
  have hmapD : D₀.map f=P := map_comap_eq_self_of_surjective hf _
  have hkD : f.ker ≤ D₀ := by
    intro y hy
    change f y ∈ P
    rw [MonoidHom.mem_ker.mp hy]
    exact P.one_mem
  obtain ⟨j,hj,hjr,hjR,hjQ,hjU⟩ := Sp4Four.LocalPackage.edge_coordinates d.radical
    (h.replacement_two_group d) (h.replacement_core_le d) path.start_color hat
  have hQT : Q d.radical a ≤ Q d.radical t := by
    rw [←hjQ,←hjR]
    exact map_mono (h.replacement_core_le d)
  have hkJ : f.ker ≤ J₀ := by
    intro y hy
    have hyQ : y.val ∈ Q d.radical a := hfQ ▸ mem_map_of_mem S.subtype hy
    change y.val ∈ J
    rw [←hsat]
    exact ⟨hQT hyQ,mem_map_of_mem S.subtype (hkD hy)⟩
  have hcard : Nat.card B.Carrier = Nat.card F := by rw [B.card_eq,hB,h.field_card]
  have hcJ : Nat.card B.Carrier^2 ≤ Nat.card (J₀.map f) := by
    rw [←relIndex_ker]
    have hh := relIndex_map_map_of_injective f.ker J₀ S.subtype_injective
    rw [hfQ,map_subgroupOf_eq_of_le hJS] at hh
    rw [←hh,hcard]
    exact h.replacement_small_mover_join_index d geometry hb path.start_color hat
  obtain ⟨hcA,hdA⟩ := root_image_from_indices h d path hb hsmall B hB f hfQ hindex
  have hq : 2 < Nat.card B.Carrier := by
    rw [B.card_eq,hB]
    exact lt_of_lt_of_le (by decide : 2 < 2^2) (Nat.pow_le_pow_right (by decide) h.nonbinary)
  obtain ⟨g₀,x₀,hgen₀,hpair₀,hpos₀⟩ := SmallPlaneGeneration.exists_subplane_root_generators hq
    P (J₀.map f) (A₀.map f) ⟨1,by
      rw [show (MulAut.conj (1 : Sp B.Carrier)).toMonoidHom = MonoidHom.id _ by ext y; simp,
        Subgroup.map_id]⟩ ((map_le_iff_le_comap).mpr hJplane)
    (map_mono (comap_mono hzJ)) (by nlinarith) hcA hdA
  have hL : L₀.map f=⊤ := by
    have he : L₀=pResidual 2 S := comap_map_eq_self_of_injective S.subtype_injective _
    rw [he,map_pResidual_of_surjective 2 f hf]
    let : Group.IsPerfect (Sp B.Carrier) := perfect_of_card_gt_two hq
    exact pResidual_eq_top_of_isPerfect 2
  obtain ⟨g,hg,hfg⟩ := (show g₀ ∈ L₀.map f by rw [hL]; trivial)
  obtain ⟨x,hx,hfx⟩ := (show x₀ ∈ L₀.map f by rw [hL]; trivial)
  have hgen : (J₀.map (MulAut.conj g).toMonoidHom ⊔ A₀) ⊔
      A₀.map (MulAut.conj x).toMonoidHom = ⊤ := by
    apply full_of_full_image f _ ((kernel_le_conjugate f J₀ hkJ g).trans
      (le_sup_left.trans le_sup_left))
    rwa [Subgroup.map_sup,Subgroup.map_sup,Subgroup.image_conjugate,Subgroup.image_conjugate,hfg,hfx]
  have hpair : D₀.map (MulAut.conj g).toMonoidHom ⊔
      (D₀.map (MulAut.conj g).toMonoidHom).map (MulAut.conj x⁻¹).toMonoidHom = ⊤ := by
    apply full_of_full_image f _ ((kernel_le_conjugate f D₀ hkD g).trans le_sup_left)
    rwa [Subgroup.map_sup,Subgroup.image_conjugate,Subgroup.image_conjugate,Subgroup.image_conjugate,
      hmapD,hfg,map_inv,hfx]
  have hgen' := congrArg (Subgroup.map S.subtype) hgen
  rw [Subgroup.map_sup,Subgroup.map_sup,Subgroup.image_conjugate,Subgroup.image_conjugate,
    map_subgroupOf_eq_of_le hJS,map_subgroupOf_eq_of_le hzS,
    ←MonoidHom.range_eq_map,range_subtype] at hgen'
  have hpair' := congrArg (Subgroup.map S.subtype) hpair
  rw [Subgroup.map_sup,Subgroup.image_conjugate,Subgroup.image_conjugate,Subgroup.image_conjugate,
    ←MonoidHom.range_eq_map,range_subtype] at hpair'
  have hxN : x ∈ normalizer (D₀ : Set S) := by
    apply P.le_normalizer_comap f
    change f x ∈ normalizer (P : Set (Sp B.Carrier))
    rw [hfx]
    exact hpos₀
  have hxD : x.val ∈ normalizer (D : Set (FreeAmalgam d.radical)) :=
    D₀.le_normalizer_map S.subtype (mem_map_of_mem S.subtype hxN)
  have hxP := D₀.le_normalizer_map f (mem_map_of_mem f hxN)
  rw [hmapD,show P=planeRadicalAmbient from SymplecticConjugatePair.planeRadical_eq_wing.symm,
    planeRadicalAmbient_normalizer B.card_eq (by rw [hB]; exact h.nonbinary)] at hxP
  refine ⟨g.val,hg,x.val,hx,hgen',hpair',?_,hxD,⟨x,hxP,rfl⟩⟩
  have he := h.replacement_small_mover_parabolic_full_fixed d geometry hb path.start_color hat
    B hB f hf hfQ hindex hJplane
  have he₁ := conjugate_fixed_eq (Z d.radical a) J D he g.val
    (Z_normalized d.radical a g.property)
  have he₂ := conjugate_fixed_eq (Z d.radical a) _ _ he₁ x.val⁻¹
    (Z_normalized d.radical a (S.inv_mem x.property))
  apply le_antisymm
  · intro w hw
    have hw₁ := he₁ ▸ hw.1
    have hw₂ := he₂ ▸ (show w ∈ Z d.radical a ⊓ centralizer
      ((J.map (MulAut.conj g.val).toMonoidHom).map (MulAut.conj x.val⁻¹).toMonoidHom :
        Set (FreeAmalgam d.radical)) from ⟨hw.1.1,hw.2⟩)
    refine ⟨hw.1.1,?_⟩
    have h₁ : D.map (MulAut.conj g.val).toMonoidHom ≤ centralizer ({w} : Set (FreeAmalgam d.radical)) :=
      fun y hy => mem_centralizer_singleton_iff.mpr (hw₁.2 y hy)
    have h₂ : (D.map (MulAut.conj g.val).toMonoidHom).map (MulAut.conj x.val⁻¹).toMonoidHom ≤
        centralizer ({w} : Set (FreeAmalgam d.radical)) :=
      fun y hy => mem_centralizer_singleton_iff.mpr (hw₂.2 y hy)
    intro y hy
    exact mem_centralizer_singleton_iff.mp ((sup_le h₁ h₂) (hpair'.symm ▸ hy))
  · intro w hw
    have hJg : J.map (MulAut.conj g.val).toMonoidHom ≤ S := le_sup_left.trans le_sup_left |>.trans_eq hgen'
    have hJgx : (J.map (MulAut.conj g.val).toMonoidHom).map (MulAut.conj x.val⁻¹).toMonoidHom ≤ S := by
      rintro y ⟨v,hv,rfl⟩
      exact S.mul_mem (S.mul_mem (S.inv_mem x.property) (hJg hv)) (S.inv_mem (S.inv_mem x.property))
    exact ⟨⟨hw.1,centralizer_le hJg hw.2⟩,centralizer_le hJgx hw.2⟩

/-- The actual maximizing-parabolic construction now supplies generation
by J in its literal J ≤ Q₁ branch, with the same selector's whole-layer
fixed subgroup and parabolic placement. All model premises are discharged. -/
theorem Input.replacement_maximizing_parabolic_small_root_selection
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
         (J.subgroupOf (stabilizer d.radical a) ≤ Q₁ →
           Q d.radical t ⊓ D = J ∧
           Z d.radical z ≤ J ∧
           ((Z d.radical z).subgroupOf (stabilizer d.radical a)).map f <
             (J.subgroupOf (stabilizer d.radical a)).map f ∧
           U d.radical a ⊓ centralizer (J : Set (FreeAmalgam d.radical)) =
             U d.radical a ⊓ centralizer (D : Set (FreeAmalgam d.radical))) ∧
         ∃ g ∈ Ltilde d.radical a, ∃ x ∈ Ltilde d.radical a,
           (D.map (MulAut.conj g).toMonoidHom ⊔ Z d.radical z) ⊔
             (Z d.radical z).map (MulAut.conj x).toMonoidHom = stabilizer d.radical a ∧
           ((Z d.radical a ⊓ centralizer (D.map (MulAut.conj g).toMonoidHom : Set (FreeAmalgam d.radical))) ⊓
             centralizer ((D.map (MulAut.conj g).toMonoidHom).map
               (MulAut.conj x⁻¹).toMonoidHom : Set (FreeAmalgam d.radical)) =
               Z d.radical a ⊓ centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical))) ∧
           x ∈ normalizer (D : Set (FreeAmalgam d.radical)) ∧
           x ∈ (planeParabolic.comap f).map (stabilizer d.radical a).subtype ∧
           (J.subgroupOf (stabilizer d.radical a) ≤ Q₁ →
             ((J.map (MulAut.conj g).toMonoidHom ⊔ Z d.radical z) ⊔
               (Z d.radical z).map (MulAut.conj x).toMonoidHom = stabilizer d.radical a) ∧
             ((Z d.radical a ⊓ centralizer (J.map (MulAut.conj g).toMonoidHom : Set (FreeAmalgam d.radical))) ⊓
               centralizer ((J.map (MulAut.conj g).toMonoidHom).map
                 (MulAut.conj x⁻¹).toMonoidHom : Set (FreeAmalgam d.radical)) =
                 Z d.radical a ⊓ centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical))))) := by
  classical
  obtain ⟨B,hB,f,hf,hfQ,hTf,hindex,hcore,hTP,hquad,hmax,hsep,hbranch,
    g,hg,x,hx,hgen,hfixed,hxn,hxp,hJfixed⟩ :=
    h.replacement_maximizing_parabolic_root_mover d path hb hat hfirst hsmall
  let S := stabilizer d.radical a
  let D := (((CentralRootGeometry.wing (F := B.Carrier) true).map unipotent.subtype).comap f).map S.subtype
  let J := Subgroup.SmallMover.join (U d.radical a) (Q d.radical a) (Q d.radical t) (Nat.card F^2)
  by_cases hJplane : J.subgroupOf S ≤
      ((CentralRootGeometry.wing (F := B.Carrier) true).map unipotent.subtype).comap f
  · obtain ⟨g,hg,x,hx,hgenJ,hpair,hJfixed,hxn,hxp⟩ :=
      h.replacement_smaller_mover_root_selection d path hb hat hfirst hsmall
        B hB f hf hfQ hTf hindex hJplane
    have hsat : Q d.radical t ⊓ D = J := (hbranch hJplane).1
    have hJD : J ≤ D := by rw [←hsat]; exact inf_le_right
    have hDS : D ≤ S := (map_le_range _ _).trans_eq (range_subtype _)
    have hDg : D.map (MulAut.conj g).toMonoidHom ≤ S := by
      rintro y ⟨v,hv,rfl⟩
      have hgS := Ltilde_le_stabilizer a hg
      exact S.mul_mem (S.mul_mem hgS (hDS hv)) (S.inv_mem hgS)
    have hgenD : (D.map (MulAut.conj g).toMonoidHom ⊔ Z d.radical z) ⊔
        (Z d.radical z).map (MulAut.conj x).toMonoidHom = S := by
      apply le_antisymm
      · exact sup_le (sup_le hDg ((le_sup_right.trans le_sup_left).trans_eq hgenJ))
          (le_sup_right.trans_eq hgenJ)
      · exact hgenJ.ge.trans (sup_le_sup_right (sup_le_sup_right (map_mono hJD) _) _)
    refine ⟨B,hB,f,hf,hfQ,hTf,hindex,hcore,hTP,hquad,hmax,hsep,hbranch,
      g,hg,x,hx,hgenD,?_,hxn,hxp,fun _ => ⟨hgenJ,hJfixed⟩⟩
    exact fixed_pair_of_generation (Z d.radical a) _ _ _ hpair
  · exact ⟨B,hB,f,hf,hfQ,hTf,hindex,hcore,hTP,hquad,hmax,hsep,hbranch,
      g,hg,x,hx,hgen,hfixed,hxn,hxp,fun hh => (hJplane hh).elim⟩

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
