module

public import Theory.AtlasPort.LinearGroups.G2.BinaryParabolicPair
public import Theory.AtlasPort.LinearGroups.G2.BinaryParabolicPair.DerivedGroup
public import Theory.AtlasPort.LinearGroups.G2.BinaryParabolicPair.CoreIdentification
public import Theory.AtlasPort.LinearGroups.G2.BinaryParabolicPair.DerivedCore
public import Theory.GroupTheory.PGroup.SubnormalCore
public import Mathlib.GroupTheory.Abelianization.Defs

/-!
# Restricting the binary parabolic core to the derived group

The long-root quotient sends the five-root coordinates to the parity c+d.
Thus the core intersects the actual commutator subgroup in the explicit
Q₈ ◦ C₄ subgroup. Normality and monotonicity of the two-core identify this
intersection with the two-core of the restricted first parabolic. The actual
core isomorphism retains the residual cubic and its central quotient action.
The restricted pair has the original intersection embeddings; its Sylow and
standard geometric markings are separate statements.
Source: Aschbacher–Smith, Lemma 14.2.21, printed p.988.
-/

@[expose] public section

namespace Atlas.G2.BinaryParabolicPair
open Atlas.G2.Explicit BinaryCore
open scoped commutatorElement
set_option maxRecDepth 100000
set_option maxHeartbeats 400000

theorem project_embedding (x : Coordinates) :
    BinaryException.projection (embedding x) =
      if x.c=x.d then 1 else BinaryException.quotientBit := by
  change BinaryException.projection (unipotentProduct (parameters x)) = _
  simp only [unipotentProduct, parameters, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three,
    map_mul, BinaryException.project_A, BinaryException.project_B,
    BinaryException.project_E, one_mul, mul_one,
    BinaryException.project_C_eq_D, BinaryException.project_D_eq_F]
  change BinaryException.projection (rootF x.c) * BinaryException.projection (rootF x.d) *
    BinaryException.projection (rootF 0) = _
  rw [rootF_zero,map_one,mul_one]
  rw [← map_mul, rootF_add]
  by_cases h : x.c=x.d
  · rw [if_pos h]
    have hz : x.c+x.d=0 := (by decide +kernel :
      ∀ c d : ZMod 2, c=d → c+d=0) x.c x.d h
    rw [hz,rootF_zero,map_one]
  · rw [if_neg h]
    have ho : x.c+x.d=1 := (by decide +kernel :
      ∀ c d : ZMod 2, c≠d → c+d=1) x.c x.d h
    rw [ho]
    rfl

theorem embedding_mem_derived_iff (x : Coordinates) :
    embedding x ∈ commutator (Model (ZMod 2)) ↔ x.c=x.d := by
  rw [commutator_eq_longRootClosure, ← QuotientGroup.eq_one_iff]
  change BinaryException.projection (embedding x) = 1 ↔ x.c=x.d
  rw [project_embedding]
  split_ifs with h
  · simp [h]
  · simp [h,quotientBit_ne_one]

/-- The derived-group core is the actual intersection, not just an abstract model. -/
theorem derivedCore_eq_intersection :
    derivedCore = core ⊓ commutator (Model (ZMod 2)) := by
  ext g
  constructor
  · rintro ⟨x,hx,rfl⟩
    exact ⟨⟨x,rfl⟩, (embedding_mem_derived_iff x).mpr hx⟩
  · rintro ⟨⟨x,rfl⟩,hx⟩
    exact ⟨x, (embedding_mem_derived_iff x).mp hx, rfl⟩

def derivedFirstAmbient : Subgroup (Model (ZMod 2)) :=
  firstParabolic ⊓ commutator (Model (ZMod 2))

def derivedSecondAmbient : Subgroup (Model (ZMod 2)) :=
  secondParabolic ⊓ commutator (Model (ZMod 2))

def derivedSylowAmbient : Subgroup (Model (ZMod 2)) :=
  unipotent ⊓ commutator (Model (ZMod 2))

theorem derived_parabolic_intersection :
    derivedFirstAmbient ⊓ derivedSecondAmbient = derivedSylowAmbient := by
  rw [derivedFirstAmbient,derivedSecondAmbient,inf_inf_inf_comm,inf_idem,
    parabolic_intersection]
  rfl

theorem derivedCore_le_first : derivedCore ≤ derivedFirstAmbient := by
  rw [derivedCore_eq_intersection]
  exact inf_le_inf core_le_firstParabolic le_rfl

instance derivedCore_normal : (derivedCore.subgroupOf derivedFirstAmbient).Normal := by
  rw [derivedCore_eq_intersection]
  exact Subgroup.inf_subgroupOf_inf_normal_of_left _

/-- The Q₈ ◦ C₄ model is exactly the first restricted parabolic's two-core. -/
theorem derivedFirst_pCore : derivedFirstAmbient.pCoreIn 2 = derivedCore := by
  apply le_antisymm
  · rw [derivedCore_eq_intersection]
    apply le_inf
    · have hn : (derivedFirstAmbient.subgroupOf firstParabolic).Normal := by
        change ((firstParabolic ⊓ commutator (Model (ZMod 2))).subgroupOf firstParabolic).Normal
        rw [Subgroup.inf_subgroupOf_left]
        infer_instance
      have hm := pCoreAmbient_mono_of_isSubnormalIn derivedFirstAmbient firstParabolic 2
        inf_le_left hn.isSubnormal
      exact hm.trans firstParabolic_pCore.le
    · exact (Subgroup.pCoreIn_le 2 derivedFirstAmbient).trans inf_le_right
  · exact Subgroup.le_pCoreIn_of_normalizes
      (IsPGroup.of_card (show Nat.card derivedCore = 2^4 from card_derivedCore))
      derivedCore_le_first
      ((Subgroup.normal_subgroupOf_iff_le_normalizer derivedCore_le_first).mp inferInstance)

/-- The restricted pair is formed inside the actual derived group. -/
abbrev DerivedModel := commutator (Model (ZMod 2))

def derivedFirst : Subgroup DerivedModel := firstParabolic.subgroupOf _
def derivedSecond : Subgroup DerivedModel := secondParabolic.subgroupOf _

noncomputable def derivedFirstEquiv : derivedFirst ≃* derivedFirstAmbient where
  toFun x := ⟨x.val.val,x.prop,x.val.prop⟩
  invFun x := ⟨⟨x.val,x.prop.2⟩,x.prop.1⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

theorem derivedFirst_pCore_in_model :
    (derivedFirst.pCoreIn 2).map DerivedModel.subtype = derivedCore := by
  rw [← derivedFirst_pCore]
  have he := pCore_map_iso 2 derivedFirstEquiv
  have hh := congrArg (Subgroup.map derivedFirstAmbient.subtype) he
  have hf : derivedFirstAmbient.subtype.comp derivedFirstEquiv.toMonoidHom =
      DerivedModel.subtype.comp derivedFirst.subtype := by ext x; rfl
  simpa only [Subgroup.pCoreIn, Subgroup.map_map, hf] using hh

noncomputable def derivedFirstCoreEquiv : QuaternionCyclic.Model ≃*
    (derivedFirst.pCoreIn 2).map DerivedModel.subtype :=
  derivedCoreEquiv.trans (MulEquiv.subgroupCongr derivedFirst_pCore_in_model.symm)

theorem cubicActor_mem_derived : cubicActor ∈ commutator (Model (ZMod 2)) := by
  rw [commutator_eq_longRootClosure, ← BinaryException.lineSign_kernel]
  have hpow : Binary.lineSign cubicActor ^ 3 = 1 := by
    rw [← map_pow, cubicActor_cube, map_one]
  have hs : Binary.lineSign cubicActor = 1 ∨ Binary.lineSign cubicActor = -1 :=
    Int.units_eq_one_or _
  rcases hs with h | h
  · exact h
  · rw [h] at hpow
    norm_num at hpow

theorem cubicActor_mem_derivedFirst :
    (⟨cubicActor,cubicActor_mem_derived⟩ : DerivedModel) ∈ derivedFirst := cubicActor_mem

theorem cubicActor_derived_residual :
    (⟨⟨cubicActor,cubicActor_mem_derived⟩,cubicActor_mem_derivedFirst⟩ : derivedFirst) ∈
      pResidual 2 derivedFirst := by
  apply Subgroup.mem_sInf.mpr
  rintro N ⟨hN,hP⟩
  let := hN
  let a : derivedFirst := ⟨⟨cubicActor,cubicActor_mem_derived⟩,cubicActor_mem_derivedFirst⟩
  let b := QuotientGroup.mk' N a
  have hb3 : b^3=1 := by
    change (QuotientGroup.mk' N a)^3=1
    rw [← map_pow, show a^3=1 from Subtype.ext (Subtype.ext cubicActor_cube), map_one]
  obtain ⟨k,hk⟩ := hP b
  apply (QuotientGroup.eq_one_iff a).mp
  change b=1
  apply orderOf_eq_one_iff.mp
  exact Nat.eq_one_of_dvd_coprimes (show Nat.Coprime 3 (2^k) from
    (by decide : Nat.Coprime 3 2).pow_right k)
    (orderOf_dvd_of_pow_eq_one hb3) (orderOf_dvd_of_pow_eq_one hk)

theorem derivedFirstCoreEquiv_apply (x : QuaternionCyclic.Model) :
    (derivedFirstCoreEquiv x : Model (ZMod 2)) = embedding (quaternionCyclicEmbedding x) := rfl

theorem cubic_derivedFirstCore (x : QuaternionCyclic.Model) :
    cubicActor * (derivedFirstCoreEquiv x : Model (ZMod 2)) * cubicActor⁻¹ =
      (derivedFirstCoreEquiv (QuaternionCyclic.cubic x) : Model (ZMod 2)) :=
  cubic_derivedCore x

/-- The central quotient on the actual embedded two-core of the derived first parabolic. -/
noncomputable def derivedFirstCoreCentralQuotient :
    (derivedFirst.pCoreIn 2).map DerivedModel.subtype →* QuaternionCyclic.CentralQuotient :=
  QuaternionCyclic.centralQuotient.comp derivedFirstCoreEquiv.symm.toMonoidHom

theorem derivedFirstCoreCentralQuotient_apply (x : QuaternionCyclic.Model) :
    derivedFirstCoreCentralQuotient (derivedFirstCoreEquiv x) =
      QuaternionCyclic.centralQuotient x := by
  simp [derivedFirstCoreCentralQuotient]

theorem derivedFirstCoreCentralQuotient_surjective :
    Function.Surjective derivedFirstCoreCentralQuotient :=
  QuaternionCyclic.centralQuotient_surjective.comp derivedFirstCoreEquiv.symm.surjective

theorem derivedFirstCoreCentralQuotient_ker :
    derivedFirstCoreCentralQuotient.ker =
      Subgroup.center ((derivedFirst.pCoreIn 2).map DerivedModel.subtype) := by
  ext g
  change derivedFirstCoreEquiv.symm g ∈ QuaternionCyclic.centralQuotient.ker ↔
    g ∈ Subgroup.center _
  rw [QuaternionCyclic.centralQuotient_ker, Subgroup.mem_center_iff, Subgroup.mem_center_iff]
  constructor
  · intro hg h
    apply derivedFirstCoreEquiv.symm.injective
    simpa only [map_mul] using hg (derivedFirstCoreEquiv.symm h)
  · intro hg q
    apply derivedFirstCoreEquiv.injective
    simpa only [map_mul, MulEquiv.apply_symm_apply] using hg (derivedFirstCoreEquiv q)

theorem derivedFirstCoreCentralQuotient_cubic (x : QuaternionCyclic.Model) :
    derivedFirstCoreCentralQuotient (derivedFirstCoreEquiv (QuaternionCyclic.cubic x)) =
      QuaternionCyclic.cubicQuotient
        (derivedFirstCoreCentralQuotient (derivedFirstCoreEquiv x)) := by
  simp only [derivedFirstCoreCentralQuotient_apply, QuaternionCyclic.cubic_centralQuotient]

/-- An intrinsic isomorphism from O₂ of the first parabolic in G₂(2)′. -/
noncomputable def derivedIntrinsicCoreEquiv :
    pCore 2 derivedFirst ≃* QuaternionCyclic.Model :=
  ((pCore 2 derivedFirst).equivMapOfInjective derivedFirst.subtype
    Subtype.coe_injective).trans
      (((derivedFirst.pCoreIn 2).equivMapOfInjective DerivedModel.subtype
        Subtype.coe_injective).trans derivedFirstCoreEquiv.symm)

end Atlas.G2.BinaryParabolicPair
