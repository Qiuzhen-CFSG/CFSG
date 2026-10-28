module
public import CFSG.Quasithin.ChapterB.Section01.SolvableStructure.ThreeConjugates.Reduction
public import CFSG.Quasithin.ChapterB.Section01.SolvableStructure.ThreeConjugates.StableImage
public import Theory.GroupAction.CommutingFixedKernel
public import Mathlib.RepresentationTheory.Invariants
public import Mathlib.FieldTheory.Finiteness

/-!
# The fixed space of the relative two-core

For a faithful finite-dimensional binary action, a normal three-subgroup N
with two-group quotient forces C_G(C_V(O₂(G)))=O₂(G). The two-core commutes
with N. The P × Q lemma makes the pointwise kernel in N a two-group, hence
trivial. The whole kernel then embeds in G/N and is a normal two-subgroup.

Applied to H=K⊔T and N=⟨Kᵀ⟩, this constructs the surjection to the actual
linear action image on U=C_V(O₂(H)), identifies its kernel, and constructs
H/O₂(H)≃*Aut_H(U) compatibly with the quotient map. The image is solvable
and has trivial two-core. No FF or factor-decomposition hypothesis is used.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
B.1.12 and the fixed-space argument in B.1.10, printed pp. 72–73
(PDF pp. 83–84).
-/

@[expose] public section
namespace CFSG.Quasithin.ChapterB.ThreeConjugates
open Representation.BinaryOffender Subgroup
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

private def multiplicativeAction : G →* MulAut (Multiplicative V) where
  toFun g := AddEquiv.toMultiplicative
    (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) V (ρ.asGroupHom g)).toAddEquiv
  map_one' := by ext v; exact congrArg Multiplicative.ofAdd (congrArg (fun f => f v.toAdd) ρ.map_one)
  map_mul' g h := by ext v; exact congrArg Multiplicative.ofAdd (congrArg (fun f => f v.toAdd) (ρ.map_mul g h))

private theorem multiplicativeAction_injective (hf : Function.Injective ρ) :
    Function.Injective (multiplicativeAction ρ) := by
  intro g h he
  apply hf
  ext v
  exact congrArg (fun f : MulAut (Multiplicative V) => (f (Multiplicative.ofAdd v)).toAdd) he

private instance : IsElementaryAbelian 2 (Multiplicative V) where
  exponent_dvd_p := by
    apply Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
    intro v
    change (2 : ℕ) • v.toAdd = 0
    calc
      (2 : ℕ) • v.toAdd = (2 : ZMod 2) • v.toAdd :=
        (Nat.cast_smul_eq_nsmul (ZMod 2) 2 v.toAdd).symm
      _ = 0 := by rw [show (2 : ZMod 2) = 0 by decide, zero_smul]

/-- A normal subgroup has an invariant fixed space. -/
theorem fixedSpace_stable (Q : Subgroup G) [Q.Normal] :
    (⊤ : Subgroup G) ≤ subspaceStabilizer ρ (fixedSpace ρ Q) :=
  le_subspaceStabilizer ρ _ (fun g _ _ hv => Representation.le_comap_invariants ρ Q g hv)

/-- The action of the whole group on the fixed space of a normal subgroup. -/
noncomputable def fixedSpaceActionHom (Q : Subgroup G) [Q.Normal] :
    G →* subspaceActionImage ρ (fixedSpace ρ Q) :=
  (subgroupActionHom ρ (fixedSpace ρ Q) ⊤ (fixedSpace_stable ρ Q)).comp
    Subgroup.topEquiv.symm.toMonoidHom

@[simp] theorem fixedSpaceActionHom_apply (Q : Subgroup G) [Q.Normal] (g : G)
    (v : fixedSpace ρ Q) :
    (subspaceImageRepresentation ρ (fixedSpace ρ Q) (fixedSpaceActionHom ρ Q g) v : V) =
      ρ g v := rfl

theorem fixedSpaceActionHom_surjective (Q : Subgroup G) [Q.Normal] :
    Function.Surjective (fixedSpaceActionHom ρ Q) := by
  intro x
  obtain ⟨g, rfl⟩ := (stabilizerRepresentation ρ (fixedSpace ρ Q)).asGroupHom.rangeRestrict_surjective x
  exact ⟨g, rfl⟩

theorem fixedSpaceActionHom_ker (Q : Subgroup G) [Q.Normal] :
    (fixedSpaceActionHom ρ Q).ker = subspaceKernel ρ (fixedSpace ρ Q) ⊤ := by
  ext g
  constructor
  · intro hg
    refine ⟨mem_top g, fun v hv => ?_⟩
    have he := congrArg (fun a => subspaceImageRepresentation ρ (fixedSpace ρ Q) a ⟨v, hv⟩) hg
    exact congrArg Subtype.val he
  · rintro ⟨_, hg⟩
    apply subspaceImageRepresentation_injective ρ (fixedSpace ρ Q)
    ext v
    exact hg v v.property

variable [Finite G] [FiniteDimensional (ZMod 2) V]

omit [Finite G] in
private theorem commuting_fixed_kernel_isTwoGroup (hf : Function.Injective ρ)
    (Q A : Subgroup G) (hQ : IsPGroup 2 Q) (hQA : ⁅Q, A⁆ = ⊥) :
    IsPGroup 2 (subspaceKernel ρ (fixedSpace ρ Q) A) := by
  let : Finite V := Module.finite_of_finite (ZMod 2)
  let f := multiplicativeAction ρ
  let B := subspaceKernel ρ (fixedSpace ρ Q) A
  have hc : ⁅Q.map f, B.map f⁆ = ⊥ := by
    rw [← map_commutator]
    have hb : ⁅Q, B⁆ = ⊥ := le_bot_iff.mp
      ((commutator_mono le_rfl (subspaceKernel_le ρ _ A)).trans hQA.le)
    rw [hb, Subgroup.map_bot]
  have hfix : B.map f ≤ fixingSubgroup (MulAut (Multiplicative V))
      (FixedPoints.subgroup (Q.map f) (Multiplicative V) : Set (Multiplicative V)) := by
    rintro _ ⟨b, hb, rfl⟩
    rw [mem_fixingSubgroup_iff]
    intro v hv
    have hv' : v.toAdd ∈ fixedSpace ρ Q := by
      intro q
      exact congrArg Multiplicative.toAdd (hv ⟨f q, mem_map_of_mem f q.property⟩)
    exact congrArg Multiplicative.ofAdd (hb.2 v.toAdd hv')
  have hp := isPGroup_of_commuting_fixes_fixed (Q.map f) (B.map f) (hQ.map f) hc hfix
  exact hp.of_injective (f.subgroupMap B) (fun x y h => Subtype.ext
    (multiplicativeAction_injective ρ hf (congrArg Subtype.val h)))

omit [Finite G] in
/-- For a normal three-subgroup with two-group quotient, the fixed-space
kernel of the two-core is exactly that two-core. -/
theorem fixedSpace_kernel_eq_twoCore (hf : Function.Injective ρ)
    (N : Subgroup G) [N.Normal] (hN : IsPGroup 3 N) (hq : IsPGroup 2 (G ⧸ N)) :
    subspaceKernel ρ (fixedSpace ρ (pCore 2 G)) ⊤ = pCore 2 G := by
  let Q := pCore 2 G
  let B := subspaceKernel ρ (fixedSpace ρ Q) ⊤
  have hQN : ⁅Q, N⁆ = ⊥ := commutator_eq_bot_of_disjoint
    (pCore_isPGroup.disjoint_of_coprime hN (by decide : Nat.Coprime 2 3))
  have hsmall : subspaceKernel ρ (fixedSpace ρ Q) N = ⊥ := by
    have h2 := commuting_fixed_kernel_isTwoGroup ρ hf Q N pCore_isPGroup hQN
    have h3 := hN.to_le (subspaceKernel_le ρ (fixedSpace ρ Q) N)
    exact disjoint_self.mp (h2.disjoint_of_coprime h3 (by decide : Nat.Coprime 2 3))
  have hinj : Function.Injective ((QuotientGroup.mk' N).comp B.subtype) := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    apply bot_unique
    intro b hb
    have hn : (b : G) ∈ N := (QuotientGroup.eq_one_iff (N := N) b).mp hb
    apply Subtype.ext
    exact mem_bot.mp (hsmall ▸ (show (b : G) ∈ subspaceKernel ρ (fixedSpace ρ Q) N
      from ⟨hn, b.property.2⟩))
  have hB : IsPGroup 2 B := hq.of_injective _ hinj
  have hnormal : B.Normal := by
    apply normalizer_eq_top_iff.mp
    apply top_le_iff.mp
    exact (normal_subgroupOf_iff_le_normalizer (show B ≤ ⊤ from le_top)).mp
      (subspaceKernel_normal ρ _ ⊤ (fixedSpace_stable ρ Q))
  apply le_antisymm
  · exact le_sSup ⟨hnormal, hB⟩
  · intro q hq
    exact ⟨mem_top q, fun _ hv => hv ⟨q, hq⟩⟩

/-- Restrict the original representation to the actual local group H. -/
def localRepresentation (K T : Subgroup G) : Representation (ZMod 2) (K ⊔ T : Subgroup G) V :=
  ρ.comp (K ⊔ T).subtype

/-- The fixed space U=C_V(O₂(H)), computed inside H. -/
noncomputable def localFixedSpace (K T : Subgroup G) : Submodule (ZMod 2) V :=
  fixedSpace (localRepresentation ρ K T) (pCore 2 (K ⊔ T : Subgroup G))

/-- The actual surjection from H to its action image on U. -/
noncomputable def localActionHom (K T : Subgroup G) :
    (K ⊔ T : Subgroup G) →* subspaceActionImage (localRepresentation ρ K T) (localFixedSpace ρ K T) :=
  fixedSpaceActionHom (localRepresentation ρ K T) (pCore 2 (K ⊔ T : Subgroup G))

/-- The kernel equality in the proof of B.1.12. -/
theorem localActionHom_ker (hf : Function.Injective ρ) (K T : Subgroup G)
    (hK : (K.subgroupOf (K ⊔ T)).IsSubnormal) (hcard : Nat.card K = 3)
    (hT : IsPGroup 2 T) :
    (localActionHom ρ K T).ker = pCore 2 (K ⊔ T : Subgroup G) := by
  refine (fixedSpaceActionHom_ker (localRepresentation ρ K T) (pCore 2 (K ⊔ T : Subgroup G))).trans ?_
  let := conjugateClosure_normal K T
  exact fixedSpace_kernel_eq_twoCore (localRepresentation ρ K T)
    (hf.comp (K ⊔ T).subtype_injective)
    ((conjugateClosure K T).subgroupOf (K ⊔ T))
    (conjugateClosure_isThreeGroup K T hK hcard).comap_subtype
    (quotient_conjugateClosure_isTwoGroup K T hT)

/-- The faithful action image is explicitly H/O₂(H). -/
noncomputable def localActionQuotientEquiv (hf : Function.Injective ρ) (K T : Subgroup G)
    (hK : (K.subgroupOf (K ⊔ T)).IsSubnormal) (hcard : Nat.card K = 3)
    (hT : IsPGroup 2 T) :
    ((K ⊔ T : Subgroup G) ⧸ pCore 2 (K ⊔ T : Subgroup G)) ≃*
      subspaceActionImage (localRepresentation ρ K T) (localFixedSpace ρ K T) :=
  (QuotientGroup.quotientMulEquivOfEq (localActionHom_ker ρ hf K T hK hcard hT).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective (localActionHom ρ K T)
      (fixedSpaceActionHom_surjective _ _))

@[simp] theorem localActionQuotientEquiv_mk (hf : Function.Injective ρ) (K T : Subgroup G)
    (hK : (K.subgroupOf (K ⊔ T)).IsSubnormal) (hcard : Nat.card K = 3)
    (hT : IsPGroup 2 T) (g : (K ⊔ T : Subgroup G)) :
    localActionQuotientEquiv ρ hf K T hK hcard hT
      (QuotientGroup.mk' (pCore 2 (K ⊔ T : Subgroup G)) g) = localActionHom ρ K T g := by
  simp [localActionQuotientEquiv, QuotientGroup.quotientMulEquivOfEq_mk,
    QuotientGroup.quotientKerEquivOfSurjective]

omit [FiniteDimensional (ZMod 2) V] in
/-- The image group is solvable. -/
theorem localActionImage_solvable (K T : Subgroup G)
    (hK : (K.subgroupOf (K ⊔ T)).IsSubnormal) (hcard : Nat.card K = 3)
    (hT : IsPGroup 2 T) :
    Group.IsSolvable (subspaceActionImage (localRepresentation ρ K T) (localFixedSpace ρ K T)) := by
  let := local_solvable K T hK hcard hT
  exact Group.isSolvable_of_surjective (fixedSpaceActionHom_surjective (localRepresentation ρ K T) _)

/-- The image group has trivial two-core. -/
theorem localActionImage_twoCore (hf : Function.Injective ρ) (K T : Subgroup G)
    (hK : (K.subgroupOf (K ⊔ T)).IsSubnormal) (hcard : Nat.card K = 3)
    (hT : IsPGroup 2 T) :
    pCore 2 (subspaceActionImage (localRepresentation ρ K T) (localFixedSpace ρ K T)) = ⊥ := by
  let f := localActionHom ρ K T
  have hker := localActionHom_ker ρ hf K T hK hcard hT
  have hsurj := fixedSpaceActionHom_surjective (localRepresentation ρ K T) (pCore 2 (K ⊔ T : Subgroup G))
  have h2 := pCore_isPGroup.comap_of_ker_isPGroup f (hker.symm ▸ pCore_isPGroup)
  have hle : (pCore 2 _).comap f ≤ f.ker := by
    rw [hker]
    exact le_sSup ⟨inferInstance, h2⟩
  apply bot_unique
  intro x hx
  obtain ⟨g, rfl⟩ := hsurj x
  exact hle hx

end CFSG.Quasithin.ChapterB.ThreeConjugates
