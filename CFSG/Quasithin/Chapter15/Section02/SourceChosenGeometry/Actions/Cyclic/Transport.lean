module
public import CFSG.Quasithin.Chapter15.Section02.SourceChosenGeometry.Actions
public import CFSG.Quasithin.Chapter15.Section02.SourceChosenGeometry.Offenders.Numerics

/-!
# Fixed and moved source planes

The coordinates are the original elements of V with additive notation. They
identify fixed subspaces with ambient relative centralizers and moved subspaces
with the actual subgroup commutators. The no-FF four-space theorem makes a
quadratic elementary image cyclic of order two and gives both subspaces
dimension two, so they coincide. Full support then places Ω₁Z(T) in the plane.
When this image is the whole Sylow image, the plane equals Ω₁Z(T).

Source: Aschbacher--Smith 15.2.13(2) and 15.2.14(2), printed pp.1111--1112,
combined manuscript of 1 March 2004, refs/quasithin.pdf.
-/

public section
open scoped IsMulCommutative
open Subgroup Representation Representation.BinaryOffender Stellmacher Theory.GroupTheory
open CFSG.Quasithin.ChapterD CFSG.Quasithin.ChapterD.UniqueFactor
namespace CFSG.Quasithin.Chapter15.Section02.ChosenGeometry.Cyclic
variable {G : Type*} [Group G]

/-- A subspace of the literal chosen module, embedded back into G. -/
@[expose] noncomputable def ambientSpace (V : Subgroup G) [IsElementaryAbelian 2 V]
    (W : Submodule (ZMod 2) (Additive V)) : Subgroup G :=
  (Subgroup.toAddSubgroup.symm W.toAddSubgroup).map V.subtype

theorem mem_ambientSpace {V : Subgroup G} [IsElementaryAbelian 2 V]
    (W : Submodule (ZMod 2) (Additive V)) (v : V) :
    (v : G) ∈ ambientSpace V W ↔ Additive.ofMul v ∈ W := by
  constructor
  · rintro ⟨w, hw, he⟩
    exact (Subtype.ext he : w = v) ▸ hw
  · intro hv
    exact ⟨v,hv,rfl⟩

theorem ambientSpace_fixed {M V B : Subgroup G} [IsElementaryAbelian 2 V]
    (hn : M ≤ normalizer (V : Set G)) (hBM : B ≤ M) :
    ambientSpace V (fixedSpace (imageRepresentation M V hn) (actor M V B hn)) =
      V ⊓ centralizer (B : Set G) := by
  ext v
  constructor
  · rintro ⟨w,hw,rfl⟩
    refine ⟨w.property,fun b hb => ?_⟩
    have he := hw ⟨(actionHom M V hn).rangeRestrict ⟨b,hBM hb⟩,
      mem_map_of_mem _ hb⟩
    have hv := congrArg (fun x : Additive V => (x.toMul : G)) he
    change b * (w : G) * b⁻¹ = w at hv
    exact mul_inv_eq_iff_eq_mul.mp hv
  · rintro ⟨hv,hc⟩
    refine ⟨⟨v,hv⟩,?_,rfl⟩
    rintro ⟨_,b,hb,rfl⟩
    apply Additive.toMul.injective
    apply Subtype.ext
    change (b : G) * v * (b : G)⁻¹ = v
    rw [hc b hb,mul_inv_cancel_right]

private noncomputable def coordinates (M V : Subgroup G)
    [IsElementaryAbelian 2 V] (hn : M ≤ normalizer (V : Set G)) (hVM : V ≤ M) :
    BinaryConjugationSection M V ⊥ ((imageRepresentation M V hn).comp
      (actionHom M V hn).rangeRestrict) where
  section_le := hVM
  kernel_le := bot_le
  normalized := hn
  coordinates := {
    toFun v := Multiplicative.ofAdd (Additive.ofMul v)
    map_one' := rfl
    map_mul' := fun _ _ => rfl }
  onto := fun v => ⟨v.toAdd.toMul,rfl⟩
  kernel_eq := by ext x; exact Subtype.val_inj.symm
  equivariant := fun _ _ => rfl

private theorem ambientSpace_coordinates {M V : Subgroup G}
    [IsElementaryAbelian 2 V] (hn : M ≤ normalizer (V : Set G)) (hVM : V ≤ M)
    (E : Subgroup G) (hEV : E ≤ V) :
    ambientSpace V ((coordinates M V hn hVM).imageSpace E) = E := by
  ext v
  constructor
  · rintro ⟨w,hw,rfl⟩
    obtain ⟨x,hx,he⟩ := ((coordinates M V hn hVM).mem_imageSpace_iff E _).mp hw
    have hh : (x : G) = (w : G) := congrArg (fun a : Additive V => (a.toMul : G)) he
    change (w : G) ∈ E
    rw [←hh]
    exact hx
  · intro hv
    refine ⟨⟨v,hEV hv⟩,?_,rfl⟩
    exact ((coordinates M V hn hVM).mem_imageSpace_iff E _).mpr
      ⟨⟨v,hEV hv⟩,hv,rfl⟩

set_option backward.isDefEq.respectTransparency false in
theorem ambientSpace_moved {M V B : Subgroup G} [IsElementaryAbelian 2 V]
    (hn : M ≤ normalizer (V : Set G)) (hVM : V ≤ M) (hBM : B ≤ M) :
    ambientSpace V (subspaceCommutator (imageRepresentation M V hn) ⊤
      (actor M V B hn)) = ⁅V,B⁆ := by
  let c := coordinates M V hn hVM
  have ht : c.imageSpace V = ⊤ := by
    apply top_unique
    intro v _
    exact (c.mem_imageSpace_iff _ _).mpr ⟨v.toMul,v.toMul.property,rfl⟩
  have he := c.imageSpace_commutator B V hBM le_rfl
  rw [commutator_comm,ht,subspaceCommutator_comp_map] at he
  change ambientSpace V (subspaceCommutator _ ⊤ ((B.subgroupOf M).map _)) = _
  rw [←he]
  exact ambientSpace_coordinates hn hVM _
    (le_normalizer_iff_commutator_le_left.mp (hBM.trans hn))

variable [Finite G]
open Section01 Section03 Section03.InitialSource ChapterA.Section05To06
/-- The no-FF four-space forces every nontrivial quadratic elementary actor to
have equal fixed and moved planes. No restricted-model premise is used. -/
theorem quadratic_fixed_eq_moved {T : Sylow 2 G} {M Mc V : Subgroup G}
    (h : ChosenSmallSource T M Mc V) :
    letI := h.prepared.elementary
    ∀ A : Subgroup (internalActionImage M V h.prepared.normalized),
      IsElementaryTwo A → IsQuadratic (imageRepresentation M V h.prepared.normalized) A →
      Nat.card A = 2 ∧ fixedSpace (imageRepresentation M V h.prepared.normalized) A =
        subspaceCommutator (imageRepresentation M V h.prepared.normalized) ⊤ A := by
  let := h.prepared.elementary
  intro A hA hq
  obtain ⟨hr,hcod⟩ := h.quadratic_actor A hA hq
  have hc : Nat.card A = 2 := by simpa only [hr,pow_one] using hA.card_eq_two_pow_rank
  refine ⟨hc,?_⟩
  symm
  apply Submodule.eq_of_le_of_finrank_eq
  · apply Submodule.span_le.mpr
    rintro _ ⟨b,hb,v,_,rfl⟩ a
    exact hq a a.property b hb v
  · let : IsCyclic A := isCyclic_of_prime_card hc
    obtain ⟨a,he⟩ := A.isCyclic_iff_exists_zpowers_eq_top.mp inferInstance
    rw [←he,CyclicFixedRank.commutator_eq_range,←fixedCodim_zpowers_eq_displacement_rank,he]
    have hd := fixedCodim_add_finrank (imageRepresentation M V h.prepared.normalized) A
    rw [h.finrank_eq_four,hcod] at hd
    omega

/-- The fixed/moved equality transported through the actual conjugation image. -/
theorem ambient_fixed_eq_commutator {T : Sylow 2 G} {M Mc V B : Subgroup G}
    (h : ChosenSmallSource T M Mc V) (hBM : B ≤ M)
    (hA : IsElementaryTwo (actor M V B h.prepared.normalized))
    (hq : letI := h.prepared.elementary
      IsQuadratic (imageRepresentation M V h.prepared.normalized)
        (actor M V B h.prepared.normalized)) :
    V ⊓ centralizer (B : Set G) = ⁅V,B⁆ := by
  let := h.prepared.elementary
  have he := (quadratic_fixed_eq_moved h _ hA hq).2
  have hm := congrArg (ambientSpace V) he
  rwa [ambientSpace_fixed _ hBM,
    ambientSpace_moved _ h.prepared.le_selected hBM] at hm

/-- Full support puts Ω₁Z(T) in every source quadratic commutator plane. -/
theorem seed_le_commutator {T : Sylow 2 G} {M Mc V B : Subgroup G}
    (h : ChosenSmallSource T M Mc V) (hfull : V = localModule T M)
    (hBT : B ≤ (T : Subgroup G))
    (hA : IsElementaryTwo (actor M V B h.prepared.normalized))
    (hq : letI := h.prepared.elementary
      IsQuadratic (imageRepresentation M V h.prepared.normalized)
        (actor M V B h.prepared.normalized)) : centralInvolutions T ≤ ⁅V,B⁆ := by
  rw [←ambient_fixed_eq_commutator h (hBT.trans h.maximal.1.2) hA hq]
  exact le_inf (by rw [hfull]; exact le_conjugateSpanBy _ _)
    ((centralInvolutions_le_centralizer_sylow T).trans (centralizer_le hBT))
/-- When the common involution image is the whole Sylow image, the plane is
exactly Ω₁Z(T), giving the equal-plane alternative of 15.2.14(2). -/
theorem equal_plane_of_full_sylow_image {T : Sylow 2 G} {M Mc V B : Subgroup G}
    (h : ChosenSmallSource T M Mc V) (hfull : V = localModule T M)
    (hBT : B ≤ (T : Subgroup G))
    (hA : IsElementaryTwo (actor M V B h.prepared.normalized))
    (hq : letI := h.prepared.elementary
      IsQuadratic (imageRepresentation M V h.prepared.normalized)
        (actor M V B h.prepared.normalized))
    (he : actor M V B h.prepared.normalized =
      actor M V (T : Subgroup G) h.prepared.normalized) :
    planeCentralizer T ⁅V,B⁆ = (T : Subgroup G) ∧ centralInvolutions T = ⁅V,B⁆ := by
  let := h.prepared.elementary
  have hf : V ⊓ centralizer (B : Set G) = V ⊓ centralizer ((T : Subgroup G) : Set G) := by
    rw [←ambientSpace_fixed h.prepared.normalized (hBT.trans h.maximal.1.2),
      ←ambientSpace_fixed h.prepared.normalized h.maximal.1.2,he]
  have hc : ⁅V,B⁆ = V ⊓ centralizer ((T : Subgroup G) : Set G) :=
    (ambient_fixed_eq_commutator h (hBT.trans h.maximal.1.2) hA hq).symm.trans hf
  have hz : centralInvolutions T = ⁅V,B⁆ := by
    apply le_antisymm (seed_le_commutator h hfull hBT hA hq)
    rw [hc]
    intro v hv
    exact (mem_omegaOneCenterAmbient_iff _ v).mpr
      ⟨h.le_sylow hv.1,elemPow_eq_one_of_isElementaryAbelian (p := 2) v hv.1,
        fun t ht => hv.2 t ht⟩
  refine ⟨?_,hz⟩
  apply inf_eq_left.mpr
  exact le_centralizer_iff.mpr (hc.le.trans inf_le_right)

end CFSG.Quasithin.Chapter15.Section02.ChosenGeometry.Cyclic
