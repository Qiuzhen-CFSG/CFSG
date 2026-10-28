module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.MaximizingParabolic
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.RootImage
public import Theory.SpecificGroups.SymplecticFour.SelectedPlaneGeneration
public import Theory.GroupTheory.MarkedConjugateGeneration
public import Theory.GroupTheory.PResidual.PerfectImage
public import Theory.Representation.ConjugationFixedQuotient
public import Theory.Representation.SymplecticConjugatePair.ElementaryGeometry.NaturalFixed
public import Theory.SpecificGroups.SymplecticFour.LocalStructure.ParabolicCores

/-!
# The full-plane branch of the nonbinary source selection

At every original field degree, an order-q-cubed small mover is a whole
plane radical. The reciprocal critical comparison recognizes a critical
image of order below q squared as a full long root. One matrix selector
then gives both the three source generators and a generating pair of full
plane radicals. Lifting both through the entire Q-kernel proves the exact
common fixed subgroup on the whole Z-layer, including all central factors.

For the actual maximizing parabolic, the source containment J <= Q1 and
the order-q-cubed case identify J with that literal two-core. On the chosen
critical path, the endpoint lies in J. The same original residual selector
therefore belongs to the chosen parabolic, without an extra containment
premise. This proves the generation, full fixed-layer and positioning
clauses in this full-plane, field-sized-critical-image branch of MS93
(5.6)(b--d), printed pp.917--918.

Proper subgroups of the plane radical, larger critical images, (5.5),
the terminal exclusions and the distance-two witness remain separate
obligations. No replacement odd-index radical witness is assumed.
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

private theorem lift_selection {S T : Type*} [Group S] [Group T]
    (f : S →* T) (L E A : Subgroup S) (hL : L.map f=⊤) (hk : f.ker ≤ E)
    (g₀ x₀ : T)
    (hgen : ((E.map f).map (MulAut.conj g₀).toMonoidHom ⊔ A.map f) ⊔
      (A.map f).map (MulAut.conj x₀).toMonoidHom = ⊤)
    (hpair : (E.map f).map (MulAut.conj g₀).toMonoidHom ⊔
      ((E.map f).map (MulAut.conj g₀).toMonoidHom).map (MulAut.conj x₀⁻¹).toMonoidHom = ⊤)
    (hpos : A.map f ≤ E.map f → x₀ ∈ normalizer (E.map f : Set T)) :
    ∃ g ∈ L, ∃ x ∈ L,
      (E.map (MulAut.conj g).toMonoidHom ⊔ A) ⊔ A.map (MulAut.conj x).toMonoidHom = ⊤ ∧
      (E.map (MulAut.conj g).toMonoidHom ⊔
        (E.map (MulAut.conj g).toMonoidHom).map (MulAut.conj x⁻¹).toMonoidHom = ⊤) ∧
      (A ≤ E → x ∈ normalizer (E : Set S)) := by
  obtain ⟨g,hg,hfg⟩ := (show g₀ ∈ L.map f by rw [hL]; trivial)
  obtain ⟨x,hx,hfx⟩ := (show x₀ ∈ L.map f by rw [hL]; trivial)
  have hkg := kernel_le_conjugate f E hk g
  refine ⟨g,hg,x,hx,?_,?_,?_⟩
  · apply full_of_full_image f _ (hkg.trans (le_sup_left.trans le_sup_left))
    rwa [Subgroup.map_sup,Subgroup.map_sup,Subgroup.image_conjugate,
      Subgroup.image_conjugate,hfg,hfx]
  · apply full_of_full_image f _ (hkg.trans le_sup_left)
    rwa [Subgroup.map_sup,Subgroup.image_conjugate,Subgroup.image_conjugate,
      Subgroup.image_conjugate,hfg,map_inv,hfx]
  · intro hAE
    have hxN : f x ∈ normalizer (E.map f : Set T) := hfx ▸ hpos (map_mono hAE)
    have hn := (E.map f).le_normalizer_comap f hxN
    rwa [comap_map_eq_self hk] at hn

variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

/-- The full-plane branch of the source selector at the unchanged degree.
The same original conjugators generate with the endpoint, and their full
plane pair generates the entire stabilizer, retaining the whole Q-kernel. -/
theorem Input.replacement_cubic_mover_root_selection
    {geometry : Geometry d.radical} {a z : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : 4 ≤ geometry.b d.radical)
    (hsmall : (Q d.radical a).relIndex (Z d.radical z) < Nat.card F^2)
    (E : Subgroup (FreeAmalgam d.radical)) (hES : E ≤ stabilizer d.radical a)
    (hQE : Q d.radical a ≤ E) (hpE : IsPGroup 2 E)
    (hEc : (Q d.radical a).relIndex E = Nat.card F^3)
    (hEm : (centralizer (E : Set (FreeAmalgam d.radical))).relIndex (U d.radical a) ≤ Nat.card F^2) :
    ∃ g ∈ Ltilde d.radical a, ∃ x ∈ Ltilde d.radical a,
      (E.map (MulAut.conj g).toMonoidHom ⊔ Z d.radical z) ⊔
        (Z d.radical z).map (MulAut.conj x).toMonoidHom = stabilizer d.radical a ∧
      (E.map (MulAut.conj g).toMonoidHom ⊔
        (E.map (MulAut.conj g).toMonoidHom).map (MulAut.conj x⁻¹).toMonoidHom = stabilizer d.radical a) ∧
      (Z d.radical z ≤ E → x ∈ normalizer (E : Set (FreeAmalgam d.radical))) := by
  obtain ⟨B,hB,f,hf,hfQ,π,hπ,hπker,hact⟩ :=
    h.replacement_inner_natural_action d geometry hb path.start_color
  have hBF : Nat.card B.Carrier = Nat.card F := by rw [B.card_eq,hB,h.field_card]
  let S := stabilizer d.radical a
  let E₀ := E.subgroupOf S
  let A₀ := (Z d.radical z).subgroupOf S
  let L₀ := (Ltilde d.radical a).subgroupOf S
  let := finite_stabilizer d.radical a
  have hzS := path.endpoint_Z_le_start_stabilizer (by omega : 0 < geometry.b d.radical)
  have hQeq : f.ker = (Q d.radical a).subgroupOf S := by
    apply map_injective S.subtype_injective
    rw [hfQ,map_subgroupOf_eq_of_le (show Q d.radical a ≤ S from fun _ hx => hx.1)]
  have hkE : f.ker ≤ E₀ := by rw [hQeq]; exact comap_mono hQE
  have hEcard : Nat.card (E₀.map f) = Nat.card B.Carrier^3 := by
    rw [←relIndex_ker,hQeq]
    have he := relIndex_map_map_of_injective ((Q d.radical a).subgroupOf S) E₀ S.subtype_injective
    rw [map_subgroupOf_eq_of_le (show Q d.radical a ≤ S from fun _ hx => hx.1),
      map_subgroupOf_eq_of_le hES] at he
    rw [←he,hEc,hBF]
  have hEn : E ≤ normalizer (U d.radical a : Set (FreeAmalgam d.radical)) := hES.trans (U_normalized a)
  let δE := f.comp (inclusion hES)
  have hδE : δE.range = E₀.map f := by
    rw [MonoidHom.range_comp]
    congr 1
    ext y
    exact ⟨fun ⟨x,hx⟩ => hx ▸ x.property,fun hy => ⟨⟨y.val,hy⟩,rfl⟩⟩
  let := finite_Z d.radical a
  let : Finite (U d.radical a) := Finite.of_injective (inclusion (U_le_Z a)) (inclusion_injective _)
  have hEmodel : Nat.card (Vector B.Carrier ⧸ fixedSpace
      (restrictScalars (k := ZMod 2) (symplecticNatural (k := B.Carrier) 2)) (E₀.map f)) ≤ Nat.card B.Carrier^2 := by
    have hh := Representation.fixed_quotient_card_le_centralizer_index (U d.radical a) E hEn π hπ
      (restrictScalars (k := ZMod 2) (symplecticNatural (k := B.Carrier) 2)) δE
      (fun x u => hact (inclusion hES x) u)
    rw [hδE] at hh
    rw [hBF]
    exact hh.trans hEm
  obtain ⟨k,hk⟩ := SelectedPlaneGeneration.conjugate_plane_of_cubic_order B.card_eq
    (by rw [hB]; exact Nat.zero_lt_one.trans h.nonbinary) (E₀.map f) (hpE.comap_subtype.map f) hEcard hEmodel
  let rev : CriticalPath d.radical geometry z a :=
    { start_color := path.end_color
      walk := path.walk.reverse
      shortest := by rw [SimpleGraph.Walk.length_reverse,path.shortest,SimpleGraph.dist_comm]
      critical := critical_reverse d.radical geometry
        (MSCentralOrbit.edgeCentralizerCondition d.radical (h.replacement_two_group d)
          (h.replacement_core_le d) (h.replacement_omegaOrbit_centralizer d))
        a path.start_color (by rw [geometry.distance_constant a path.start_color]; exact (show 0 < geometry.b d.radical by omega))
        z path.end_color path.critical }
  let δ := f.comp (inclusion hzS)
  have hδ : δ.range = A₀.map f := by
    rw [MonoidHom.range_comp]
    congr 1
    ext y
    exact ⟨fun ⟨x,hx⟩ => hx ▸ x.property,fun hy => ⟨⟨y.val,hy⟩,rfl⟩⟩
  have hδcard : Nat.card δ.range = (Q d.radical a).relIndex (Z d.radical z) :=
    Sp4Four.SourceComparison.quotient_image_card _ _ _ hzS f hfQ
  obtain ⟨hc,hd,hq⟩ := h.replacement_small_critical_root_image d hBF rev
    (by omega) π hπ δ hδcard (fun x u => hact (inclusion hzS x) u) hsmall
  rw [hδ] at hc hd hq
  obtain ⟨g₀,x₀,hgen,hpair,hpos⟩ := SelectedPlaneGeneration.exists_plane_root_generators
    (E₀.map f) (A₀.map f) ⟨k,hk⟩ hc hd hq
  have hL : L₀.map f=⊤ := by
    have he : L₀=pResidual 2 S := comap_map_eq_self_of_injective S.subtype_injective _
    rw [he,map_pResidual_of_surjective 2 f hf]
    let : Group.IsPerfect (Sp B.Carrier) := perfect_of_card_gt_two (by
      rw [hBF,h.field_card]
      exact lt_of_lt_of_le (by decide : 2 < 2^2) (Nat.pow_le_pow_right (by decide) h.nonbinary))
    exact pResidual_eq_top_of_isPerfect 2
  obtain ⟨g,hg,x,hx,hgen,hpair,hpos⟩ := lift_selection f L₀ E₀ A₀ hL hkE g₀ x₀ hgen hpair hpos
  refine ⟨g.val,hg,x.val,hx,?_,?_,?_⟩
  · have hm := congrArg (Subgroup.map S.subtype) hgen
    rw [Subgroup.map_sup,Subgroup.map_sup,Subgroup.image_conjugate,Subgroup.image_conjugate,
      map_subgroupOf_eq_of_le hES,map_subgroupOf_eq_of_le hzS,
      ←MonoidHom.range_eq_map,range_subtype] at hm
    exact hm
  · have hm := congrArg (Subgroup.map S.subtype) hpair
    rw [Subgroup.map_sup,Subgroup.image_conjugate,Subgroup.image_conjugate,Subgroup.image_conjugate,
      map_subgroupOf_eq_of_le hES,←MonoidHom.range_eq_map,range_subtype] at hm
    exact hm
  · intro hzE
    have hn := E₀.le_normalizer_map S.subtype (mem_map_of_mem S.subtype (hpos (comap_mono hzE)))
    rwa [map_subgroupOf_eq_of_le hES] at hn



/-- Apply the selector to the literal small-mover join in the full-plane,
field-sized critical-image branch. The common fixed subgroup is exactly
its full ambient-central part, including every central attachment. -/
theorem Input.replacement_cubic_small_mover_root_selection
    {geometry : Geometry d.radical} {a z t : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : 4 ≤ geometry.b d.radical)
    (hat : Adjacent d.radical a t)
    (hsmall : (Q d.radical a).relIndex (Z d.radical z) < Nat.card F^2)
    (hJc : (Q d.radical a).relIndex (Subgroup.SmallMover.join (U d.radical a)
      (Q d.radical a) (Q d.radical t) (Nat.card F^2)) = Nat.card F^3)
    (hJm : (centralizer (Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
      (Q d.radical t) (Nat.card F^2) : Set (FreeAmalgam d.radical))).relIndex
        (U d.radical a) ≤ Nat.card F^2) :
    let J := Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
      (Q d.radical t) (Nat.card F^2)
    ∃ g ∈ Ltilde d.radical a, ∃ x ∈ Ltilde d.radical a,
      (J.map (MulAut.conj g).toMonoidHom ⊔ Z d.radical z) ⊔
        (Z d.radical z).map (MulAut.conj x).toMonoidHom = stabilizer d.radical a ∧
      ((Z d.radical a ⊓ centralizer (J.map (MulAut.conj g).toMonoidHom : Set (FreeAmalgam d.radical))) ⊓
        centralizer ((J.map (MulAut.conj g).toMonoidHom).map
          (MulAut.conj x⁻¹).toMonoidHom : Set (FreeAmalgam d.radical)) =
          Z d.radical a ⊓ centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical))) ∧
      (Z d.radical z ≤ J → x ∈ normalizer (J : Set (FreeAmalgam d.radical))) := by
  dsimp only
  let J := Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
    (Q d.radical t) (Nat.card F^2)
  obtain ⟨j,hj,hjr,hjR,hjQ,hjU⟩ := Sp4Four.LocalPackage.edge_coordinates d.radical
    (h.replacement_two_group d) (h.replacement_core_le d) path.start_color hat
  have hJT : J ≤ Q d.radical t := Subgroup.SmallMover.join_le _ _ _ _
  have hTS : Q d.radical t ≤ stabilizer d.radical a := by
    rw [←hjr,←hjR]
    exact map_le_range j _
  have hQJ : Q d.radical a ≤ J := by
    have hh := map_mono (f := j) (Subgroup.SmallMover.kernel_le_join
      (Sp4Four.LocalPackage.initialLayer d.radical) (pCore 2 d.overgroup) d.radical
      (Nat.card F^2) (Nat.one_le_pow _ _ Nat.card_pos) (h.replacement_core_le d)
      (Sp4Four.LocalPackage.initialLayer_centralizes_core d.radical
        (h.replacement_two_group d) (h.replacement_core_le d)))
    rwa [Subgroup.SmallMover.join_map j hj,hjU,hjQ,hjR] at hh
  have hpT : IsPGroup 2 (Q d.radical t) := hjR ▸ (h.replacement_two_group d).map j
  have hpJ : IsPGroup 2 J := hpT.of_injective (inclusion hJT) (inclusion_injective _)
  obtain ⟨g,hg,x,hx,hgen,hpair,hpos⟩ := h.replacement_cubic_mover_root_selection d
    path hb hsmall J (hJT.trans hTS) hQJ hpJ hJc hJm
  refine ⟨g,hg,x,hx,hgen,?_,hpos⟩
  have hfixed : centralizer (J.map (MulAut.conj g).toMonoidHom : Set (FreeAmalgam d.radical)) ⊓
      centralizer ((J.map (MulAut.conj g).toMonoidHom).map
        (MulAut.conj x⁻¹).toMonoidHom : Set (FreeAmalgam d.radical)) =
      centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical)) := by
    apply le_antisymm
    · intro w hw s hs
      have h₁ : J.map (MulAut.conj g).toMonoidHom ≤ centralizer ({w} : Set (FreeAmalgam d.radical)) :=
        fun y hy => mem_centralizer_singleton_iff.mpr (hw.1 y hy)
      have h₂ : (J.map (MulAut.conj g).toMonoidHom).map (MulAut.conj x⁻¹).toMonoidHom ≤
          centralizer ({w} : Set (FreeAmalgam d.radical)) :=
        fun y hy => mem_centralizer_singleton_iff.mpr (hw.2 y hy)
      exact mem_centralizer_singleton_iff.mp ((sup_le h₁ h₂) (hpair.symm ▸ hs))
    · exact le_inf (centralizer_le (show J.map (MulAut.conj g).toMonoidHom ≤ stabilizer d.radical a from
        le_sup_left.trans_eq hpair))
        (centralizer_le (show (J.map (MulAut.conj g).toMonoidHom).map (MulAut.conj x⁻¹).toMonoidHom ≤
          stabilizer d.radical a from le_sup_right.trans_eq hpair))
  rw [inf_assoc,hfixed]

/-- Apply the full-plane selector under the actual chosen-parabolic
containment in (5.6). The order q cubed identifies the mover with the
whole chosen radical, and supplies its fixed-index premise. -/
theorem Input.replacement_cubic_small_mover_plane_selection
    {geometry : Geometry d.radical} {a z t : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : 4 ≤ geometry.b d.radical)
    (hat : Adjacent d.radical a t)
    (hfirst : path.walk.getVert 1 = t)
    (hsmall : (Q d.radical a).relIndex (Z d.radical z) < Nat.card F^2)
    (B : BinaryField) (hB : B.degree = n)
    (f : stabilizer d.radical a →* Sp B.Carrier)
    (hfQ : f.ker.map (stabilizer d.radical a).subtype = Q d.radical a)
    (hTf : ((Q d.radical t).subgroupOf (stabilizer d.radical a)).map f ≤ unipotent)
    (hindex : ∀ A : Subgroup (stabilizer d.radical a),
      (centralizer (A : Set (stabilizer d.radical a))).relIndex
        ((U d.radical a).subgroupOf (stabilizer d.radical a)) =
        2 ^ fixedCodim (restrictScalars (k := ZMod 2)
          (symplecticNatural (k := B.Carrier) 2)) (A.map f))
    (hJc : (Q d.radical a).relIndex (Subgroup.SmallMover.join (U d.radical a)
      (Q d.radical a) (Q d.radical t) (Nat.card F^2)) = Nat.card F^3)
    (hJplane : (Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
      (Q d.radical t) (Nat.card F^2)).subgroupOf (stabilizer d.radical a) ≤
        ((CentralRootGeometry.wing (F := B.Carrier) true).map unipotent.subtype).comap f) :
    let J := Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
      (Q d.radical t) (Nat.card F^2)
    J.subgroupOf (stabilizer d.radical a) =
      ((CentralRootGeometry.wing (F := B.Carrier) true).map unipotent.subtype).comap f ∧
    ∃ g ∈ Ltilde d.radical a, ∃ x ∈ Ltilde d.radical a,
      (J.map (MulAut.conj g).toMonoidHom ⊔ Z d.radical z) ⊔
        (Z d.radical z).map (MulAut.conj x).toMonoidHom = stabilizer d.radical a ∧
      ((Z d.radical a ⊓ centralizer (J.map (MulAut.conj g).toMonoidHom : Set (FreeAmalgam d.radical))) ⊓
        centralizer ((J.map (MulAut.conj g).toMonoidHom).map
          (MulAut.conj x⁻¹).toMonoidHom : Set (FreeAmalgam d.radical)) =
          Z d.radical a ⊓ centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical))) ∧
      x ∈ normalizer (J : Set (FreeAmalgam d.radical)) ∧
      x ∈ (planeParabolic.comap f).map (stabilizer d.radical a).subtype := by
  dsimp only
  let S := stabilizer d.radical a
  let J := Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
    (Q d.radical t) (Nat.card F^2)
  let J₀ := J.subgroupOf S
  let P := (CentralRootGeometry.wing (F := B.Carrier) true).map unipotent.subtype
  obtain ⟨j,hj,hjr,hjR,hjQ,hjU⟩ := Sp4Four.LocalPackage.edge_coordinates d.radical
    (h.replacement_two_group d) (h.replacement_core_le d) path.start_color hat
  have hJS : J ≤ S := by
    apply (Subgroup.SmallMover.join_le _ _ _ _).trans
    change Q d.radical t ≤ stabilizer d.radical a
    rw [←hjr,←hjR]
    exact map_le_range j _
  have hQJ : Q d.radical a ≤ J := by
    have hh := map_mono (f := j) (Subgroup.SmallMover.kernel_le_join
      (Sp4Four.LocalPackage.initialLayer d.radical) (pCore 2 d.overgroup) d.radical
      (Nat.card F^2) (Nat.one_le_pow _ _ Nat.card_pos) (h.replacement_core_le d)
      (Sp4Four.LocalPackage.initialLayer_centralizes_core d.radical
        (h.replacement_two_group d) (h.replacement_core_le d)))
    rwa [Subgroup.SmallMover.join_map j hj,hjU,hjQ,hjR] at hh
  have hk : f.ker ≤ J₀ := by
    intro x hx
    exact hQJ (hfQ ▸ mem_map_of_mem S.subtype hx)
  have hcard : Nat.card B.Carrier = Nat.card F := by rw [B.card_eq,hB,h.field_card]
  have hc : Nat.card (J₀.map f) = Nat.card B.Carrier^3 := by
    rw [←relIndex_ker]
    have he := relIndex_map_map_of_injective f.ker J₀ S.subtype_injective
    rw [hfQ,map_subgroupOf_eq_of_le hJS] at he
    rw [←he,hJc,hcard]
  have hm : J₀.map f=P := by
    apply eq_of_le_of_card_ge ((map_le_iff_le_comap).mpr hJplane)
    rw [hc,card_map_of_injective unipotent.subtype_injective,CentralRootGeometry.card_wing]
  have heq : J₀=P.comap f := by rw [←hm,comap_map_eq_self hk]
  have hJm : (centralizer (J : Set (FreeAmalgam d.radical))).relIndex (U d.radical a) ≤ Nat.card F^2 := by
    have hUS : U d.radical a ≤ S := (U_le_Z a).trans (Z_le_stabilizer d.radical a)
    have he := Subgroup.SmallMover.centralizer_index_map S.subtype S.subtype_injective
      ((U d.radical a).subgroupOf S) J₀
    rw [map_subgroupOf_eq_of_le hUS,map_subgroupOf_eq_of_le hJS,hindex,hm] at he
    have hp : P=SymplecticConjugatePair.planeRadical :=
      SymplecticConjugatePair.planeRadical_eq_wing.symm
    rw [hp] at he
    change (centralizer (J : Set (FreeAmalgam d.radical))).relIndex (U d.radical a) =
      2 ^ fixedCodim (SymplecticConjugatePair.binaryNatural (F := B.Carrier))
        SymplecticConjugatePair.planeRadical at he
    rw [SymplecticConjugatePair.planeRadical_natural_fixedCodim B.card_eq] at he
    rw [he,h.field_card,hB,show 2*n=n*2 by omega,pow_mul]
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
  have hzJ : Z d.radical z ≤ J := by
    have hh : A₀ ≤ J₀ := heq ▸ (map_le_iff_le_comap).mp hAz
    have hh' := map_mono (f := S.subtype) hh
    rwa [map_subgroupOf_eq_of_le hzS,map_subgroupOf_eq_of_le hJS] at hh'
  obtain ⟨g,hg,x,hx,hgen,hfixed,hposition⟩ :=
    h.replacement_cubic_small_mover_root_selection d path hb hat hsmall hJc hJm
  have hxN := hposition hzJ
  have hxS : x ∈ S := Ltilde_le_stabilizer a hx
  have hxN₀ : (⟨x,hxS⟩ : S) ∈ normalizer (J₀ : Set S) := by
    apply mem_normalizer_iff.mpr
    intro y
    change y.val ∈ J ↔ x*y.val*x⁻¹ ∈ J
    exact mem_normalizer_iff.mp hxN y.val
  have hxP := J₀.le_normalizer_map f (mem_map_of_mem f hxN₀)
  rw [hm] at hxP
  have hPrad : P=planeRadicalAmbient := SymplecticConjugatePair.planeRadical_eq_wing.symm
  rw [hPrad,planeRadicalAmbient_normalizer B.card_eq (by rw [hB]; exact h.nonbinary)] at hxP
  exact ⟨heq,g,hg,x,hx,hgen,hfixed,hxN,⟨⟨x,hxS⟩,hxP,rfl⟩⟩

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
