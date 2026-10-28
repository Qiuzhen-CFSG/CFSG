module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BTwoD
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BOneGeometry
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BTwoActionSource

/-!
# Constructing the b=2 D geometry from the natural center action

The marked Chapter 7 action on Z/Omega(Z(L)) supplies complementary
Sylow fixed spaces. Its quotient markings separate the two neighbor
cores and recover the local actor from the two critical centers.
The earlier Sylow products contain the intermediate core, giving the
two covers of D. Thus every field of the D geometry is constructed.

Full-edge maximality proves that the quotient Sylow normalizer fixes
the actual neighbor. The full-edge factorization therefore supplies an
opposite lift for every distinct neighbor. The same data supply the
actual Q/Z actor and the natural-center line index consumed by 10.6;
these are not extra assumptions on Q/Z.

The source data are earlier Chapter 6--7 conclusions, with literal
quotient maps, kernels, center coordinates, Sylows and full-edge factors.
Final source assembly retains their discharge.
Source: DGS, *Groups and Graphs* (1985), 7.1, p.126, 10.1, p.154,
and 10.4--10.6, pp.155--158.
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open Representation.RankOne.QuadraticRecognition
open scoped Pointwise MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph Noncommuting
variable {G : Type*} [Group G]

/-- The earlier marked natural center action at a b=2 critical endpoint.
This retains the intermediate neighbor core and its literal quotient image.
No D, residual, Frattini or Q/Z conclusion is included. -/
structure BTwoCenterActionData (F : Bool → Subgroup G) (v m w : Vertex F)
    (k W : Type*) [Field k] [Finite k] [CharP k 2]
    [AddCommGroup W] [Module (ZMod 2) W] where
  middle : (graph F).Adj v m
  terminal : (graph F).Adj m w
  actor : Subgroup G
  actor_le : actor ≤ stabilizer F v
  core_le : Q F v ≤ actor
  neighbor_core_le : Q F m ≤ actor
  critical_le : Z F w ≤ actor
  factor : ∀ a ∈ stabilizer F v, ∃ l ∈ actor,
    ∃ b ∈ stabilizer F v ⊓ stabilizer F m, a = l*b
  sylow : Sylow 2 (stabilizer F v)
  sylow_le_actor : (sylow : Subgroup (stabilizer F v)).map
    (stabilizer F v).subtype ≤ actor
  quotient : actor →* SL(2,k)
  onto : Function.Surjective quotient
  kernel : quotient.ker = (Q F v).subgroupOf actor
  representation : Representation (ZMod 2) SL(2,k) W
  coordinates : BinaryConjugationSection actor (Z F v) (omegaCenterIn actor)
    (representation.comp quotient)
  imageSylow : Sylow 2 SL(2,k)
  critical_image : ((Z F w).subgroupOf actor).map quotient = imageSylow
  neighbor_image : ((Q F m).subgroupOf actor).map quotient = imageSylow
  critical_product : Stellmacher.IsSylowSubgroupIn (Z F v ⊔ Q F w) (stabilizer F w)
  centralizer_intersection : Z F v ⊓ centralizer (Z F w : Set G) = Z F v ⊓ Q F w
  sharp_index : Nat.card (W ⧸ fixedSpace representation imageSylow) = (Q F w).relIndex (Z F v)
  quadratic : IsQuadratic representation imageSylow
  generated : GeneratedByFixedSpace representation imageSylow
  fixed_bot : fixedSpace representation ⊤ = ⊥

private theorem conjugate_le (L A : Subgroup G) (hA : A ≤ L) (g : L) :
    A.map (MulAut.conj (g : G)).toMonoidHom ≤ L := by
  rintro _ ⟨a,ha,rfl⟩
  exact L.mul_mem (L.mul_mem g.property (hA ha)) (L.inv_mem g.property)

private theorem quotient_conjugate (L A : Subgroup G) (hA : A ≤ L)
    {J : Type*} [Group J] (π : L →* J) (g : L) :
    ((A.map (MulAut.conj (g : G)).toMonoidHom).subgroupOf L).map π =
      ((A.subgroupOf L).map π).map (MulAut.conj (π g)).toMonoidHom := by
  have hc : (A.map (MulAut.conj (g : G)).toMonoidHom).subgroupOf L =
      (A.subgroupOf L).map (MulAut.conj g).toMonoidHom := by
    apply map_injective L.subtype_injective
    rw [map_subgroupOf_eq_of_le (conjugate_le L A hA g),map_map]
    have he : L.subtype.comp (MulAut.conj g).toMonoidHom =
        (MulAut.conj (g : G)).toMonoidHom.comp L.subtype := by ext a; rfl
    rw [he,←map_map,map_subgroupOf_eq_of_le hA]
  rw [hc,map_map,map_map]
  congr 1
  ext a
  exact π.map_mul _ _ |>.trans (by rw [map_mul,map_inv]; rfl)

private theorem sylow_disjoint_of_ne {k : Type*} [Field k] [Finite k] [CharP k 2]
    (S T : Sylow 2 SL(2,k)) (hne : S ≠ T) :
    Disjoint (S : Subgroup SL(2,k)) (T : Subgroup SL(2,k)) := by
  apply disjoint_def.mpr
  intro x hxS hxT
  by_contra hx
  have hgen := Representation.SL2SylowFixedRecognition.sylow_sup_zpowers_eq_top T S hne.symm hxT hx
  have htop : (S : Subgroup SL(2,k)) = ⊤ := by
    simpa only [sup_eq_left.mpr (zpowers_le.mpr hxS)] using hgen
  apply Matrix.SpecialLinearGroup.sylow_normalizer_ne_top S
  change normalizer ((S : Subgroup SL(2,k)) : Set SL(2,k)) = ⊤
  rw [htop]
  exact top_unique (⊤ : Subgroup SL(2,k)).le_normalizer


variable {P : Fin 2 → Subgroup G} {B : Subgroup G}
variable {k W : Type*} [Field k] [Finite k] [CharP k 2]
  [AddCommGroup W] [Module (ZMod 2) W]

/-- Construct the complete paired-D geometry from the earlier natural
center action and the two shifted critical Sylow products. -/
theorem BTwoCenterActionData.exists_dGeometry (h : LocallyRankOneTriple P B)
    (hS : ∀ x, Stellmacher.IsSylowSubgroupIn (Q (family P) x) (U (family P) x))
    (hb : b (family P) = 2) {v m w t : Vertex (family P)}
    (c : BTwoCenterActionData (family P) v m w k W)
    (g : c.actor) (hmove : (g : G) • m = t)
    (hop : c.quotient g ∉ normalizer (c.imageSylow : Set SL(2,k)))
    (hsm : Stellmacher.IsSylowSubgroupIn
      (Z (family P) t ⊔ Q (family P) m) (stabilizer (family P) m))
    (hst : Stellmacher.IsSylowSubgroupIn
      (Z (family P) m ⊔ Q (family P) t) (stabilizer (family P) t)) :
    Nonempty (BTwoDGeometry (family P) t v m w ((g : G) • w)) := by
  let := finite_endpoints h
  let F := family P
  let : Finite (Z F v) := Finite.of_injective
    (inclusion (Z_le_stabilizer F v)) (inclusion_injective _)
  let L := c.actor
  let π := c.quotient
  let σ := c.representation
  let S := c.imageSylow
  let e := c.coordinates
  let z := (g : G) • w
  have hgv : (g : G) • v = v := c.actor_le g.property
  have hne : S ≠ π g • S := fun he => hop (Sylow.smul_eq_iff_mem_normalizer.mp he.symm)
  have hcomp := sl2_sylow_fixed_isCompl σ S (π g • S) hne c.quadratic c.generated c.fixed_bot
  have hZconj : (Z F v).map (MulAut.conj (g : G)).toMonoidHom = Z F v := by
    rw [←Z_translate,hgv]
  have hQconj : (Q F v).map (MulAut.conj (g : G)).toMonoidHom = Q F v := by
    rw [←Q_translate,hgv]
  have hQt : Q F t = (Q F m).map (MulAut.conj (g : G)).toMonoidHom := by
    rw [←Q_translate,hmove]
  have hZm : Z F z ≤ L := by
    rw [Z_translate]
    exact conjugate_le L (Z F w) c.critical_le g
  have hZz : ((Z F z).subgroupOf L).map π = (π g • S : Sylow 2 SL(2,k)) := by
    rw [Z_translate,quotient_conjugate L (Z F w) c.critical_le π g,c.critical_image]
    rfl
  have hQtm : ((Q F t).subgroupOf L).map π = (π g • S : Sylow 2 SL(2,k)) := by
    rw [hQt,quotient_conjugate L (Q F m) c.neighbor_core_le π g,c.neighbor_image]
    rfl
  have hsep : D F m t ≤ Q F v := by
    intro x hx
    let xL : L := ⟨x,c.neighbor_core_le hx.1⟩
    have hxS : π xL ∈ (S : Subgroup SL(2,k)) := by
      rw [←c.neighbor_image]
      exact mem_map_of_mem π (show xL ∈ (Q F m).subgroupOf L from hx.1)
    have hxT : π xL ∈ ((π g • S : Sylow 2 SL(2,k)) : Subgroup SL(2,k)) := by
      rw [←hQtm]
      exact mem_map_of_mem π (show xL ∈ (Q F t).subgroupOf L from hx.2)
    have hxker : xL ∈ π.ker := disjoint_def.mp (sylow_disjoint_of_ne S (π g • S) hne) hxS hxT
    exact (show xL ∈ (Q F v).subgroupOf L from c.kernel ▸ hxker)
  have hgen : c.actor = (Z F w ⊔ Z F z) ⊔ Q F v := by
    let R := (Z F w ⊔ Z F z) ⊔ Q F v
    have hRL : R ≤ L := sup_le (sup_le c.critical_le hZm) c.core_le
    have hmap : (R.subgroupOf L).map π = ⊤ := by
      rw [subgroupOf_sup (sup_le c.critical_le hZm) c.core_le,
        subgroupOf_sup c.critical_le hZm,Subgroup.map_sup,Subgroup.map_sup,c.critical_image,hZz]
      apply top_unique
      apply le_trans _ le_sup_left
      rw [show ((π g • S : Sylow 2 SL(2,k)) : Subgroup SL(2,k)) =
        (S : Subgroup SL(2,k)).map (MulAut.conj (π g)).toMonoidHom from rfl,
        Matrix.SpecialLinearGroup.sylow_sup_conjugate_eq_top_of_not_mem_normalizer S hop]
    have he : R.subgroupOf L = ⊤ :=
      map_injective_of_ker_le π (by rw [c.kernel]; exact comap_mono le_sup_right)
        le_top (hmap.trans (map_top_of_surjective π c.onto).symm)
    have hm := congrArg (map L.subtype) he
    rw [map_subgroupOf_eq_of_le hRL,←MonoidHom.range_eq_map,range_subtype] at hm
    exact hm.symm
  have hsharp : Nat.card (W ⧸ fixedSpace σ (((Z F w).subgroupOf L).map π)) =
      (centralizer (Z F w : Set G)).relIndex (Z F v) := by
    rw [c.critical_image,c.sharp_index,←inf_relIndex_left (Z F v) (Q F w),
      ←inf_relIndex_left (Z F v) (centralizer (Z F w : Set G)),c.centralizer_intersection]
  have hfixed : e.imageSpace (Z F v ⊓ Q F w) = fixedSpace σ S := by
    rw [←c.centralizer_intersection,
      BinaryConjugationSection.image_centralizer_eq_fixed_of_sharp_index σ π e (Z F w) hsharp,
      c.critical_image]
  have hinter : (Z F v ⊓ Q F w).conjBy (g : G) = Z F v ⊓ Q F z := by
    rw [conjBy,map_inf _ _ _ (MulAut.conj (g : G)).injective,hZconj,←Q_translate]
  have hfixed' : e.imageSpace (Z F v ⊓ Q F z) = fixedSpace σ (π g • S : Sylow 2 SL(2,k)) := by
    rw [←hinter,e.imageSpace_conjBy _ inf_le_left g,hfixed]
    exact (Representation.SL2SylowFixedRecognition.fixedSpace_conjugate σ S (π g)).symm
  have hker : omegaCenterIn L ≤ Z F v ⊓ Q F w := by
    intro x hx
    have hxZ := e.kernel_le hx
    have hxfix : (e.coordinates ⟨x,hxZ⟩).toAdd ∈
        fixedSpace σ (((Z F w).subgroupOf L).map π) := by
      have he := (e.coordinates_eq_one_iff ⟨x,hxZ⟩).mpr hx
      rw [he]
      exact Submodule.zero_mem _
    have hxc := (BinaryConjugationSection.fixed_coordinates_iff_of_sharp_index
      σ π e (Z F w) hsharp ⟨x,hxZ⟩).mp hxfix
    exact c.centralizer_intersection ▸ (show x ∈ Z F v ⊓ centralizer (Z F w : Set G) from ⟨hxZ,hxc⟩)
  have hspan : Z F v = (Z F v ⊓ Q F w) ⊔ (Z F v ⊓ Q F z) := by
    apply e.section_eq_sup_of_imageSpace_sup_top _ _ inf_le_left inf_le_left (hker.trans le_sup_left)
    rw [hfixed,hfixed']
    exact hcomp.sup_eq_top
  have hcover := bTwo_core_cover_of_sylow_product h hS hb c.middle c.terminal c.critical_product
  have hopcover : Q F t ≤ Z F v ⊔ Q F z := by
    have hm := map_mono (f := (MulAut.conj (g : G)).toMonoidHom) hcover
    rwa [←hQt,Subgroup.map_sup,hZconj,←Q_translate] at hm
  refine ⟨{
    previous := ?_
    middle := c.middle
    terminal := c.terminal
    opposite := ?_
    actor := c.actor
    actor_generators := hgen
    factor := c.factor
    sylow := c.sylow
    sylow_le_actor := c.sylow_le_actor
    cover := inf_le_left.trans hcover
    opposite_cover := inf_le_right.trans hopcover
    center_span := hspan
    separated := hsep
    middle_sylow := hsm
    previous_sylow := hst }⟩
  · have he := (Subgroup.CosetGeometry.translationGraphIso F (g : G)).map_adj_iff.mpr c.middle.symm
    change (graph F).Adj ((g : G) • m) ((g : G) • v) at he
    rwa [hmove,hgv] at he
  · have he := (Subgroup.CosetGeometry.translationGraphIso F (g : G)).map_adj_iff.mpr c.terminal
    change (graph F).Adj ((g : G) • m) ((g : G) • w) at he
    rwa [hmove] at he

/-- The action for the actual Q/Z quotient is inherited from the same
marked actor; no separate quotient or kernel marking is required. -/
def BTwoCenterActionData.coreActionData {v m w t : Vertex (family P)}
    (c : BTwoCenterActionData (family P) v m w k W)
    (g : c.actor) (hmove : (g : G) • m = t) :
    BTwoActionData (family P) w m v t k where
  actor := c.actor
  actor_le := c.actor_le
  core_le := c.core_le
  quotient := c.quotient
  onto := c.onto
  kernel := c.kernel
  sylow := c.imageSylow
  actor_image := c.critical_image
  conjugator := g
  moves := hmove

local instance : Algebra (ZMod 2) k := ZMod.algebra k 2

/-- The earlier natural-center dimension computes the literal line index. -/
theorem BTwoCenterActionData.line_index {v m w : Vertex (family P)}
    (c : BTwoCenterActionData (family P) v m w k W)
    (E : W ≃ₗ[ZMod 2] (Fin 2 → k)) :
    (Q (family P) w).relIndex (Z (family P) v) = Nat.card k := by
  let : Finite W := Finite.of_equiv (Fin 2 → k) E.toEquiv.symm
  have hc := (sl2_natural_fixed_spaces c.representation c.imageSylow
    c.quadratic c.generated c.fixed_bot E).1
  have hquot := Submodule.card_eq_card_quotient_mul_card
    (fixedSpace c.representation c.imageSylow)
  rw [card_of_natural_coordinates E,hc,c.sharp_index,pow_two] at hquot
  exact (Nat.mul_left_cancel (Nat.card_pos : 0 < Nat.card k) hquot).symm

/-- The quotient Sylow normalizer fixes the original neighbor. This is
proved from maximality of the full edge, not added to the action data. -/
theorem BTwoCenterActionData.normalizer_fixes_neighbor (h : LocallyRankOneTriple P B)
    {v m w : Vertex (family P)} (c : BTwoCenterActionData (family P) v m w k W)
    (g : c.actor)
    (hg : c.quotient g ∈ normalizer (c.imageSylow : Set SL(2,k))) :
    (g : G) • m = m := by
  let F := family P
  let T := Q F m ⊔ Q F v
  let N := stabilizer F v ⊓ normalizer (T : Set G)
  let E := stabilizer F v ⊓ stabilizer F m
  have hT : T ≤ c.actor := sup_le c.neighbor_core_le c.core_le
  have hpre : (c.imageSylow : Subgroup SL(2,k)).comap c.quotient = T.subgroupOf c.actor := by
    rw [←c.neighbor_image,comap_map_eq,c.kernel,
      subgroupOf_sup c.neighbor_core_le c.core_le]
  have hnQ (x : Vertex F) : stabilizer F x ≤ normalizer (Q F x : Set G) :=
    (stabilizer F x).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image _ (pCore 2 _))
  have hEN : E ≤ N := le_inf inf_le_left
    ((le_inf (inf_le_right.trans (hnQ m)) (inf_le_left.trans (hnQ v))).trans
      (normalizer_inf_normalizer_le_normalizer_sup _ _))
  have hNE : N = E := by
    rcases source_edge_maximal h c.middle N hEN inf_le_left with he | he
    · exact he
    · exfalso
      have hn : stabilizer F v ≤ normalizer (T : Set G) := he ▸ inf_le_right
      have hp : IsPGroup 2 T := by
        have hnorm : Q F m ≤ normalizer (Q F v : Set G) :=
          ((source_Z_Q_U h m).2.trans
            ((ballKernel_one_le_edge F c.middle.symm).trans inf_le_right)).trans (hnQ v)
        exact (isPGroup_pCoreIn 2 (stabilizer F m)).to_sup_of_normal_right'
          (isPGroup_pCoreIn 2 (stabilizer F v)) hnorm
      have hTQ : T ≤ Q F v := le_pCoreIn_of_normalizes hp (hT.trans c.actor_le) hn
      have hmap : ((Q F m).subgroupOf c.actor).map c.quotient = ⊥ :=
        (Subgroup.map_eq_bot_iff _).mpr (by
          rw [c.kernel]
          exact comap_mono ((le_sup_left : Q F m ≤ T).trans hTQ))
      have hs : (c.imageSylow : Subgroup SL(2,k)) = ⊥ := c.neighbor_image.symm.trans hmap
      apply Matrix.SpecialLinearGroup.sylow_normalizer_ne_top c.imageSylow
      change normalizer ((c.imageSylow : Subgroup SL(2,k)) : Set SL(2,k)) = ⊤
      rw [hs,normalizer_eq_top]
  have he := congrArg (fun K : Subgroup c.actor => g ∈ K)
    (comap_normalizer_eq_of_surjective (c.imageSylow : Subgroup SL(2,k)) c.onto)
  rw [hpre,←subgroupOf_normalizer_eq hT] at he
  have hgn : (g : G) ∈ normalizer (T : Set G) := (Iff.of_eq he.symm).mpr hg
  exact ((show (g : G) ∈ E from hNE ▸ (show (g : G) ∈ N from
    ⟨c.actor_le g.property,hgn⟩))).2

/-- Every distinct source neighbor has a lift whose quotient moves the
Sylow. The full edge factorization supplies the lift, and maximality proves
that it lies outside the Sylow normalizer. -/
theorem BTwoCenterActionData.exists_opposite_lift (h : LocallyRankOneTriple P B)
    {v m w t : Vertex (family P)} (c : BTwoCenterActionData (family P) v m w k W)
    (ht : (graph (family P)).Adj v t) (hne : t ≠ m) :
    ∃ g : c.actor, (g : G) • m = t ∧
      c.quotient g ∉ normalizer (c.imageSylow : Set SL(2,k)) := by
  obtain ⟨a,ha,he⟩ := locally_transitive (family P) c.middle ht
  obtain ⟨l,hl,b,hb,hab⟩ := c.factor a ha
  have hbfix : b • m = m := hb.2
  have hlmove : l • m = t := by simpa only [hab,mul_smul,hbfix] using he
  refine ⟨⟨l,hl⟩,hlmove,?_⟩
  intro hn
  exact hne (hlmove.symm.trans (c.normalizer_fixes_neighbor h ⟨l,hl⟩ hn))

/-- The actual critical-center image fills a Sylow in the marked quotient.
Lifting it through the literal kernel gives the full-vertex Sylow product. -/
theorem BTwoCenterActionData.own_critical_product (h : LocallyRankOneTriple P B)
    {v m w : Vertex (family P)} (c : BTwoCenterActionData (family P) v m w k W) :
    Stellmacher.IsSylowSubgroupIn (Z (family P) w ⊔ Q (family P) v)
      (stabilizer (family P) v) := by
  let := finite_endpoints h
  have hk : IsPGroup 2 c.quotient.ker := by
    rw [c.kernel]
    exact (isPGroup_pCoreIn 2 (stabilizer (family P) v)).comap_subtype
  let T := c.imageSylow.comapOfKerIsPGroup c.quotient hk
    (by rw [MonoidHom.range_eq_top.mpr c.onto]; exact le_top)
  have hS : Stellmacher.IsSylowSubgroupIn
      (Z (family P) w ⊔ Q (family P) v) c.actor := by
    refine ⟨T,?_⟩
    change ((c.imageSylow : Subgroup SL(2,k)).comap c.quotient).map c.actor.subtype = _
    rw [←c.critical_image,comap_map_eq,c.kernel,Subgroup.map_sup,
      map_subgroupOf_eq_of_le c.critical_le,map_subgroupOf_eq_of_le c.core_le]
  have hle : (c.sylow : Subgroup (stabilizer (family P) v)) ≤
      c.actor.subgroupOf (stabilizer (family P) v) := by
    intro x hx
    exact c.sylow_le_actor (mem_map_of_mem _ hx)
  have hi : ¬ 2 ∣ c.actor.relIndex (stabilizer (family P) v) :=
    fun hd => c.sylow.not_dvd_index (hd.trans (index_dvd_of_le hle))
  exact sylow_in_overgroup_of_odd_relIndex _ _ _ c.actor_le hS hi

end CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile
