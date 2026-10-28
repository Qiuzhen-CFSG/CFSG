module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.SaturatedDistanceTwo.FullRadical
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.SaturatedDistanceTwo.WholeSection
public import Theory.SpecificGroups.SymplecticFour.CentralCovers.Even

/-!
# The component part of the full radical

At distance two, [Q,L] = U. Thus L/U is a perfect central cover of the
original marked Sp₄(F). Its proved trivial Schur multiplier identifies
L ∩ Q = U. The subgroup T₀ = T ∩ L consequently satisfies T = T₀Q,
T₀ ∩ Q = U and T₀ ∩ C_Q(L) = U ∩ C_Q(L), with all normality relative
to the actual full radical T. The whole-core index bound then gives
[T : T₀ C_Q(L)] = [Q : U C_Q(L)] ≤ q.

These are the full-radical comparisons at the start of MS93 (3.7),
printed p.873. The multiplier theorem supplies the intersection comparison
that the source obtains from (1.2); no field-four assumption or vanishing
of the complete fixed attachment is used.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped commutatorElement
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.SaturatedDistanceTwo
open DistanceTwoRecognition Theory.SpecificGroups.SymplecticFour

private theorem symplectic_kernel_eq_commutator
    {F E : Type*} [Field F] [Finite F] [CharP F 2] [Group E] [Group.IsPerfect E]
    (hF : 3 < Nat.card F) (f : E →* Sp F) (hf : Function.Surjective f)
    (N : Subgroup E) [N.Normal] (hN : N ≤ f.ker)
    (hc : ⁅f.ker, (⊤ : Subgroup E)⁆ ≤ N) : f.ker = N := by
  let φ := QuotientGroup.lift N f hN
  have hφ : Function.Surjective φ := QuotientGroup.lift_surjective_of_surjective N f hf hN
  have hcentral : φ.ker ≤ center (E ⧸ N) := by
    intro x hx
    obtain ⟨x,rfl⟩ := QuotientGroup.mk'_surjective N x
    have hx' : x ∈ f.ker := hx
    apply mem_center_iff.mpr
    intro y
    obtain ⟨y,rfl⟩ := QuotientGroup.mk'_surjective N y
    apply commutatorElement_eq_one_iff_mul_comm.mp
    rw [←map_commutatorElement]
    have hc' : ⁅(⊤ : Subgroup E),f.ker⁆ ≤ N := by rwa [commutator_comm]
    exact (QuotientGroup.eq_one_iff _).mpr (hc' (commutator_mem_commutator (mem_top y) hx'))
  let C : PerfectCentralCovering.Cover (E ⧸ N) (Sp F) :=
    { φ with surjective := hφ, isPerfect := inferInstance, ker_le_center := hcentral }
  have hi := CentralCovers.Even.cover_injective hF C
  apply le_antisymm _ hN
  intro x hx
  apply (QuotientGroup.eq_one_iff _).mp
  apply hi
  exact (show φ (QuotientGroup.mk' N x) = 1 from hx).trans (map_one φ).symm

private theorem residual_normalized {M : Type*} [Group M]
    (R : Subgroup M) (a : Vertex R) :
    stabilizer R a ≤ normalizer (Ltilde R a : Set (FreeAmalgam R)) := by
  have ht := le_normalizer_map (H := pResidual 2 (stabilizer R a))
    (stabilizer R a).subtype
  rw [normalizer_eq_top,←MonoidHom.range_eq_map,range_subtype] at ht
  exact ht

variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

/-- The whole intersection of the component and the two-core is U. -/
theorem component_inf_core_eq_moving
    (g : Geometry d.radical) (hb : g.b d.radical = 2)
    {a t : Vertex d.radical} (ha : color d.radical a = false)
    (c : EdgeMarking h d a t) :
    Ltilde d.radical a ⊓ Q d.radical a = U d.radical a := by
  let L₀ := Ltilde d.radical a
  let S := stabilizer d.radical a
  let A := Q d.radical a
  let N := (U d.radical a).subgroupOf L₀
  have hLS : L₀ ≤ S := Ltilde_le_stabilizer _
  have hLA : L₀ ≤ normalizer (A : Set (FreeAmalgam d.radical)) :=
    hLS.trans (Q_normalized _ _)
  have hSL : S ≤ normalizer (L₀ : Set (FreeAmalgam d.radical)) := by
    have ht := le_normalizer_map (H := pResidual 2 S) S.subtype
    rw [normalizer_eq_top,←MonoidHom.range_eq_map,range_subtype] at ht
    exact ht
  have hcomm : ⁅A,L₀⁆ = U d.radical a := replacement_core_eq_U_of_distance_two h d g hb ha
  have hUQ : U d.radical a ≤ A := by
    rw [←hcomm]
    exact le_normalizer_iff_commutator_le_left.mp hLA
  have hUL : U d.radical a ≤ L₀ := by
    rw [←hcomm]
    exact le_normalizer_iff_commutator_le_right.mp
      ((show A ≤ S from fun _ hx => hx.1).trans hSL)
  let : N.Normal := normal_subgroupOf_of_le_normalizer (hLS.trans (U_normalized a))
  let : Group.IsPerfect (K.subgroupOf d.overgroup) := (replacement_component h d).perfect
  let : Group.IsPerfect L₀ := by
    rw [show L₀ = (K.subgroupOf d.overgroup).map c.embedding from c.residual_eq.symm]
    exact Group.IsPerfect.map _
  let f := c.quotient.comp (inclusion hLS)
  have hf : Function.Surjective f := by
    intro y
    obtain ⟨k,hk⟩ := componentProjection_surjective h y
    let k' : K.subgroupOf d.overgroup := (subgroupOfEquivOfLe le_sup_left).symm k
    refine ⟨⟨c.embedding k',c.residual_eq.le (mem_map_of_mem c.embedding k'.property)⟩,?_⟩
    exact (c.component_equation k').trans hk
  have hk : f.ker = A.subgroupOf L₀ := by
    have hκ : c.quotient.ker = A.subgroupOf S := by
      change c.quotient.ker = (Q d.radical a).subgroupOf S
      rw [←c.kernel,subgroupOf_map_subtype_eq]
    rw [show f = c.quotient.comp (inclusion hLS) from rfl,
      ←MonoidHom.comap_ker,hκ,comap_inclusion_subgroupOf]
  have hN : N ≤ f.ker := by
    rw [hk]
    exact fun _ hx => hUQ hx
  have hc : ⁅f.ker,(⊤ : Subgroup L₀)⁆ ≤ N := by
    apply map_le_map_iff_of_injective L₀.subtype_injective |>.mp
    rw [map_commutator,hk,subgroupOf_map_subtype,←MonoidHom.range_eq_map,range_subtype,
      map_subgroupOf_eq_of_le hUL]
    exact (commutator_mono inf_le_left le_rfl).trans_eq hcomm
  have hF : 3 < Nat.card F := by
    rw [h.field_card]
    have hp := Nat.pow_le_pow_right (by decide : 0 < 2) h.nonbinary
    exact lt_of_lt_of_le (by decide : 3 < 2^2) hp
  have he := congrArg (fun B : Subgroup L₀ => B.map L₀.subtype)
    (symplectic_kernel_eq_commutator hF f hf N hN hc)
  rw [hk,subgroupOf_map_subtype,map_subgroupOf_eq_of_le hUL] at he
  exact (inf_comm _ _).trans he

/-- The component part of the same full edge radical. -/
@[expose] def componentRadical (a t : Vertex d.radical) : Subgroup (FreeAmalgam d.radical) :=
  Q d.radical t ⊓ Ltilde d.radical a

namespace EdgeMarking
variable {h d} {a t : Vertex d.radical} (c : EdgeMarking h d a t)
include c


omit [Finite H] [Finite F] [CharP F 2] in
/-- Both factors of the source comparison are normalized by the full radical. -/
theorem componentRadical_normalized : Q d.radical t ≤
    normalizer (componentRadical d a t : Set (FreeAmalgam d.radical)) :=
  (le_inf (Q d.radical t).le_normalizer (c.edge_le.trans (residual_normalized d.radical a))).trans
    inf_normalizer_le_normalizer_inf

omit [Finite H] [Finite F] [CharP F 2] in
/-- The full fixed attachment remains normal under the same actor. -/
theorem fixedCore_normalized : Q d.radical t ≤
    normalizer (fixedCore d.radical a : Set (FreeAmalgam d.radical)) :=
  (le_inf (c.edge_le.trans (Q_normalized _ _))
    ((c.edge_le.trans (residual_normalized d.radical a)).trans
      (normalizer_le_normalizer_centralizer (Ltilde d.radical a)))).trans
    inf_normalizer_le_normalizer_inf

/-- The whole edge factors over the component part, before choosing a
field-sized critical image. -/
theorem componentRadical_sup_core
    (g : Geometry d.radical) (hb : 0 < g.b d.radical) :
    componentRadical d a t ⊔ Q d.radical a = Q d.radical t := by
  let S := stabilizer d.radical a
  let A := (Q d.radical a).subgroupOf S
  let B := (Ltilde d.radical a).subgroupOf S
  let : A.Normal := normal_subgroupOf_of_le_normalizer (Q_normalized _ _)
  have hAS : Q d.radical a ≤ S := fun _ hx => hx.1
  have hBS : Ltilde d.radical a ≤ S := Ltilde_le_stabilizer _
  have htop : B ⊔ A = ⊤ := by
    rw [←subgroupOf_sup hBS hAS,c.residual_sup_core g hb,subgroupOf_self]
  apply le_antisymm (sup_le inf_le_left c.core_le_edge)
  intro x hx
  have hxs : (⟨x,c.edge_le hx⟩ : S) ∈ B ⊔ A := htop ▸ mem_top _
  obtain ⟨l,hl,q,hq,he⟩ := mem_sup_of_normal_right.mp hxs
  have hlT : l.val ∈ Q d.radical t := by
    have he' : l.val*q.val=x := congrArg Subtype.val he
    have hmem := (Q d.radical t).mul_mem hx
      ((Q d.radical t).inv_mem (c.core_le_edge hq))
    change x*q.val⁻¹ ∈ Q d.radical t at hmem
    simpa only [←he',mul_inv_cancel_right] using hmem
  have hmem := mul_mem (mem_sup_left (show l.val ∈ componentRadical d a t from ⟨hlT,hl⟩))
    (mem_sup_right (show q.val ∈ Q d.radical a from hq))
  have he' : l.val*q.val=x := congrArg Subtype.val he
  change l.val*q.val ∈ componentRadical d a t ⊔ Q d.radical a at hmem
  rwa [he'] at hmem

/-- This is the source equality T₀ ∩ Q = U, with no omitted fixed factor. -/
theorem componentRadical_inf_core
    (g : Geometry d.radical) (hb : g.b d.radical = 2)
    (ha : color d.radical a = false) :
    componentRadical d a t ⊓ Q d.radical a = U d.radical a := by
  calc
    _ = Ltilde d.radical a ⊓ Q d.radical a := by
      apply le_antisymm (inf_le_inf_right _ inf_le_right)
      exact fun _ hx => ⟨⟨c.core_le_edge hx.2,hx.1⟩,hx.2⟩
    _ = _ := component_inf_core_eq_moving h d g hb ha c

/-- Intersection with the complete fixed attachment is precisely the fixed
part of U. In particular, the construction has not assumed that part vanishes. -/
theorem componentRadical_inf_fixedCore
    (g : Geometry d.radical) (hb : g.b d.radical = 2)
    (ha : color d.radical a = false) :
    componentRadical d a t ⊓ fixedCore d.radical a =
      U d.radical a ⊓ fixedCore d.radical a := by
  rw [←c.componentRadical_inf_core g hb ha,inf_assoc,inf_eq_right.mpr
    (show fixedCore d.radical a ≤ Q d.radical a from inf_le_left)]

end EdgeMarking

omit h [Finite H] [Finite F] [CharP F 2] in
private theorem index_of_normal_supplement
    {G : Type*} [Group G] (T A B D : Subgroup G)
    (hgen : B ⊔ A = T) (hD : D ≤ A)
    (hTB : T ≤ normalizer (B : Set G)) (hTD : T ≤ normalizer (D : Set G)) :
    (B ⊔ D).relIndex T = ((B ⊓ A) ⊔ D).relIndex A := by
  have hAT : A ≤ T := le_sup_right.trans_eq hgen
  have hBT : B ≤ T := le_sup_left.trans_eq hgen
  have hDT : D ≤ T := hD.trans hAT
  let B' := B.subgroupOf T
  let D' := D.subgroupOf T
  let A' := A.subgroupOf T
  let : B'.Normal := normal_subgroupOf_of_le_normalizer hTB
  let : D'.Normal := normal_subgroupOf_of_le_normalizer hTD
  have hmod : (B' ⊔ D') ⊓ A' = (B' ⊓ A') ⊔ D' := by
    apply le_antisymm
    · rintro x ⟨hx,hxa⟩
      obtain ⟨b,hb,y,hy,rfl⟩ := mem_sup_of_normal_right.mp hx
      have hba : b ∈ A' := by
        have hh := A'.mul_mem hxa (A'.inv_mem (hD hy))
        simpa only [mul_inv_cancel_right] using hh
      exact mul_mem (mem_sup_left ⟨hb,hba⟩) (mem_sup_right hy)
    · exact sup_le (inf_le_inf_right _ le_sup_left)
        (le_inf le_sup_right (fun _ hx => hD hx))
  have htop : A' ⊔ (B' ⊔ D') = ⊤ := by
    apply top_unique
    have hh : B' ⊔ A' = ⊤ := by
      rw [←subgroupOf_sup hBT hAT,hgen,subgroupOf_self]
    rw [←hh]
    exact sup_le (le_sup_left.trans le_sup_right) le_sup_left
  calc
    _ = (B' ⊔ D').relIndex (⊤ : Subgroup T) := by
      rw [←subgroupOf_sup hBT hDT,relIndex_top_right]; rfl
    _ = (B' ⊔ D').relIndex A' := by rw [←htop,relIndex_sup_right]
    _ = ((B' ⊔ D') ⊓ A').relIndex A' := (inf_relIndex_right _ _).symm
    _ = ((B' ⊓ A') ⊔ D').relIndex A' := by rw [hmod]
    _ = ((B ⊓ A) ⊔ D).relIndex A := by
      change ((B ⊓ A).subgroupOf T ⊔ D.subgroupOf T).relIndex (A.subgroupOf T) = _
      rw [←subgroupOf_sup (inf_le_left.trans hBT) hDT,
        relIndex_subgroupOf hAT]

/-- The full-radical index is exactly the whole-core index, hence at most q.
This is the T₀D comparison at the beginning of MS93 (3.7), p.873. -/
theorem componentRadical_fixedCore_relIndex
    (g : Geometry d.radical) (hb : g.b d.radical = 2)
    {a t : Vertex d.radical} (ha : color d.radical a = false)
    (c : EdgeMarking h d a t) :
    (componentRadical d a t ⊔ fixedCore d.radical a).relIndex (Q d.radical t) =
        (U d.radical a ⊔ fixedCore d.radical a).relIndex (Q d.radical a) ∧
      (componentRadical d a t ⊔ fixedCore d.radical a).relIndex (Q d.radical t) ≤ 2^n := by
  have he := index_of_normal_supplement (Q d.radical t) (Q d.radical a)
    (componentRadical d a t) (fixedCore d.radical a)
    (c.componentRadical_sup_core g (by omega)) inf_le_left
    c.componentRadical_normalized c.fixedCore_normalized
  rw [c.componentRadical_inf_core g hb ha] at he
  exact ⟨he,he.trans_le (core_relIndex_natural_sup_fixed_le h d g hb ha)⟩

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.SaturatedDistanceTwo
