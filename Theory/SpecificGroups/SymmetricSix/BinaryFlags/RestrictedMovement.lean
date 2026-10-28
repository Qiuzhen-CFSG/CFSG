module
public import Theory.SpecificGroups.SymmetricSix.BinaryFlags.PointOrbits
public import Theory.Representation.BinaryPermutationSixCover.SeedPreimage
public import Theory.Representation.BinaryPermutationSixCover.Movement
public import Theory.Representation.BinaryOffender.CommutatorRank

/-!
# Restricted movement in the six-letter Borel

Let A be a nontrivial subgroup of an elementary abelian subgroup P of the
six-letter Borel. On both the natural four-space and the entire augmentation
five-space, [C_V(A),P] is fixed by the three-pair mover and has no nonzero
vector fixed by the full symmetric group.

Choose a nonidentity involution in A. Kernel-checked tables on the sixteen
Borel elements show that its fixed vectors have mover-fixed displacements,
and that every such displacement vanishes at one common coordinate. Thus
their span misses the constant line. Every natural fixed vector lifts to a
fixed augmentation vector, so the calculation also covers the quotient.
Equivariance transports both conclusions through arbitrary cover markings
and conjugated Borels. No bound on the size of A or P is required.

Source: the six-letter module calculation used in Meierfrankenfeld--
Stellmacher, Pushing up weak BN-pairs of rank two (1993), (5.12)(1),
printed pp.924--925. The original-Sylow distance-four application retains
both covers and uses the zero central intersection at the backward vertex.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender BinaryPermutation
open scoped IsMulCommutative
open Theory.SpecificGroups.SymmetricSix Theory.SpecificGroups.SymmetricSix.BinaryFlags
namespace BinaryPermutation.SixCover.BorelKernel
local notation "ρ" => coreRepresentation (Fin 6)
local notation "σ" => naturalRepresentation (Fin 6)
private def words (i : Fin 16) : S :=
  swap01^(i.val%2) * swap23^(i.val/2%2) * swap45^(i.val/4%2) *
    (Equiv.swap 2 4 * Equiv.swap 3 5)^(i.val/8)
private theorem words_complete : ∀ t : S, t ∈ borel → ∃ i : Fin 16, words i = t := by
  decide +kernel
private theorem fixed_cert : ∀ i j : Fin 16,
    words i ≠ 1 → (words i)^2 = 1 → (words j)^2 = 1 →
    words i * words j = words j * words i →
    ∀ v : Fin 6 → ZMod 2, (∑ k, v k) = 0 →
    representation (Fin 6) (words i) v = v →
    (representation (Fin 6) swap01 (representation (Fin 6) (words j) v-v) =
      representation (Fin 6) (words j) v-v) ∧
    (representation (Fin 6) swap23 (representation (Fin 6) (words j) v-v) =
      representation (Fin 6) (words j) v-v) ∧
    (representation (Fin 6) swap45 (representation (Fin 6) (words j) v-v) =
      representation (Fin 6) (words j) v-v) := by
  decide +kernel
private theorem zero_coordinate_cert : ∀ i : Fin 16,
    words i ≠ 1 → (words i)^2=1 → ∃ k : Fin 6, ∀ j : Fin 16,
    (words j)^2=1 → words i * words j = words j * words i →
    ∀ v : Fin 6 → ZMod 2, (∑ k, v k)=0 →
    representation (Fin 6) (words i) v=v →
    (representation (Fin 6) (words j) v-v) k=0 := by
  decide +kernel


private theorem core_displacement_fixed (t g : S)
    (ht : t ∈ borel) (htn : t ≠ 1) (ht2 : t^2=1)
    (hg : g ∈ borel) (hg2 : g^2=1) (hc : Commute t g)
    (v : core (Fin 6)) (hv : ρ t v=v) : ρ g v-v ∈ fixedSpace ρ D := by
  obtain ⟨i,rfl⟩ := words_complete t ht
  obtain ⟨j,rfl⟩ := words_complete g hg
  have hh (s : S) (hs : s ∈ ({swap01,swap23,swap45} : Set S)) :
      ρ s (ρ (words j) v-v)=ρ (words j) v-v := by
    apply Subtype.ext
    have hh := fixed_cert i j htn ht2 hg2 hc.eq v.val v.property (congrArg Subtype.val hv)
    rcases hs with rfl | rfl | rfl
    · exact hh.1
    · exact hh.2.1
    · exact hh.2.2
  suffices ∀ a ∈ closure ({swap01,swap23,swap45} : Set S),
      ρ a (ρ (words j) v-v)=ρ (words j) v-v from fun a => this a.val a.property
  intro a ha
  induction ha using Subgroup.closure_induction with
  | mem s hs => exact hh s hs
  | one => simp only [map_one,Module.End.one_apply]
  | mul s t _ _ hs ht => simp only [map_mul,Module.End.mul_apply,ht,hs]
  | inv s _ hs =>
      have he := congrArg (ρ s⁻¹) hs
      simpa only [←Module.End.mul_apply,←map_mul,inv_mul_cancel,map_one,
        Module.End.one_apply] using he.symm

private theorem core_kernel_disjoint (t : S)
    (ht : t ∈ borel) (htn : t ≠ 1) (ht2 : t^2=1)
    (P : Subgroup S) (hP : P ≤ borel) (h2 : ∀ g ∈ P, g^2=1)
    (hc : ∀ g ∈ P, Commute t g)
    (w : core (Fin 6))
    (hw : w ∈ subspaceCommutator ρ (fixedSpace ρ (zpowers t)) P)
    (hf : ∀ g : S, ρ g w=w) : w=0 := by
  obtain ⟨i,rfl⟩ := words_complete t ht
  obtain ⟨k,hk⟩ := zero_coordinate_cert i htn ht2
  let N := LinearMap.ker ((LinearMap.proj k).comp (core (Fin 6)).subtype)
  have hN : subspaceCommutator ρ (fixedSpace ρ (zpowers (words i))) P ≤ N := by
    apply Submodule.span_le.mpr
    rintro _ ⟨g,hg,v,hv,rfl⟩
    obtain ⟨j,rfl⟩ := words_complete g (hP hg)
    exact hk j (h2 _ hg) (hc _ hg).eq v.val v.property
      (congrArg Subtype.val ((mem_fixedSpace_zpowers_iff _ _ _).mp hv))
  have hwk : w.val k=0 := hN hw
  obtain ⟨c,hc⟩ := (mem_constants_iff w.val).mp
    ((core_fixed_iff_constant (by simp : 3 ≤ Nat.card (Fin 6)) w).mp (fun g => hf g.val))
  have hc0 : c=0 := (hc k).symm.trans hwk
  apply Subtype.ext
  funext j
  exact (hc j).trans hc0

private theorem natural_fixed_zero (w : natural (Fin 6))
    (hf : ∀ g : S, σ g w=w) : w=0 := by
  obtain ⟨v,rfl⟩ := coreToNatural_surjective w
  have hc := (core_fixed_iff_constant (by simp : 3 ≤ Nat.card (Fin 6)) v).mp
    (fun g => six_core_fixed_of_natural_fixed g.val v (hf g.val))
  rw [←Subtype.val_inj]
  exact (Submodule.Quotient.mk_eq_zero _).mpr hc

private theorem transport_movement
    {Y V : Type*} [AddCommGroup Y] [Module (ZMod 2) Y]
    [AddCommGroup V] [Module (ZMod 2) V]
    (τ : Representation (ZMod 2) S Y) (η : Representation (ZMod 2) S V)
    (f : Y →ₗ[ZMod 2] V) (hf : ∀ g v, f (τ g v)=η g (f v))
    (t : S) (P : Subgroup S) :
    (subspaceCommutator τ (fixedSpace τ (zpowers t)) P).map f ≤
      subspaceCommutator η (fixedSpace η (zpowers t)) P := by
  rw [Submodule.map_le_iff_le_comap]
  apply Submodule.span_le.mpr
  rintro _ ⟨g,hg,v,hv,rfl⟩
  change f (τ g v-v) ∈ subspaceCommutator η (fixedSpace η (zpowers t)) P
  rw [map_sub,hf]
  apply Submodule.subset_span
  refine ⟨g,hg,f v,?_,rfl⟩
  apply (mem_fixedSpace_zpowers_iff _ _ _).mpr
  rw [←hf,(mem_fixedSpace_zpowers_iff _ _ _).mp hv]

private theorem cover_kernel
    {Y : Type*} [AddCommGroup Y] [Module (ZMod 2) Y]
    (τ : Representation (ZMod 2) S Y)
    (hm : IsNaturalOrCore τ (MonoidHom.id S))
    (t : S) (ht : t ∈ borel) (htn : t ≠ 1) (ht2 : t^2=1)
    (P : Subgroup S) (hP : P ≤ borel) (h2 : ∀ g ∈ P, g^2=1)
    (hc : ∀ g ∈ P, Commute t g) :
    (subspaceCommutator τ (fixedSpace τ (zpowers t)) P ≤ fixedSpace τ D) ∧
    (∀ w ∈ subspaceCommutator τ (fixedSpace τ (zpowers t)) P,
      (∀ g : S, τ g w=w) → w=0) := by
  have hcore : subspaceCommutator ρ (fixedSpace ρ (zpowers t)) P ≤ fixedSpace ρ D := by
    apply Submodule.span_le.mpr
    rintro _ ⟨g,hg,v,hv,rfl⟩
    exact core_displacement_fixed t g ht htn ht2 (hP hg) (h2 g hg) (hc g hg)
      v ((mem_fixedSpace_zpowers_iff _ _ _).mp hv)
  have hnat : subspaceCommutator σ (fixedSpace σ (zpowers t)) P ≤ fixedSpace σ D := by
    apply Submodule.span_le.mpr
    rintro _ ⟨g,hg,v,hv,rfl⟩
    obtain ⟨v,rfl⟩ := coreToNatural_surjective v
    have hv' := six_core_fixed_of_natural_fixed t v ((mem_fixedSpace_zpowers_iff _ _ _).mp hv)
    have hh := core_displacement_fixed t g ht htn ht2 (hP hg) (h2 g hg) (hc g hg) v hv'
    intro a
    have he := congrArg (coreToNatural (Fin 6)) (hh a)
    simpa only [MonoidHom.comp_apply,map_sub,coreToNatural_equivariant] using he
  rcases hm with ⟨E,hE⟩ | ⟨E,hE⟩
  · have he : ∀ g v, E (τ g v)=σ g (E v) := hE
    have htE := transport_movement τ σ E.toLinearMap he t P
    constructor
    · intro w hw a
      apply E.injective
      exact (he a.val w).trans (hnat (htE ⟨w,hw,rfl⟩) a)
    · intro w hw hf
      apply E.injective
      rw [map_zero]
      exact natural_fixed_zero (E w) (fun g => (he g w).symm.trans (congrArg E (hf g)))
  · have he : ∀ g v, E (τ g v)=ρ g (E v) := hE
    have htE := transport_movement τ ρ E.toLinearMap he t P
    constructor
    · intro w hw a
      apply E.injective
      exact (he a.val w).trans (hcore (htE ⟨w,hw,rfl⟩) a)
    · intro w hw hf
      apply E.injective
      rw [map_zero]
      exact core_kernel_disjoint t ht htn ht2 P hP h2 hc (E w) (htE ⟨w,hw,rfl⟩)
        (fun g => (he g w).symm.trans (congrArg E (hf g)))



/-- In either full six-letter cover, movement of the fixed space of a
nontrivial subgroup of an elementary Borel actor is fixed by the proper
plane mover and has no nonzero globally fixed vector. No image-order
bound is imposed on the actor or its subgroup. -/
theorem kernel_properties
    {Y : Type*} [AddCommGroup Y] [Module (ZMod 2) Y]
    (τ : Representation (ZMod 2) S Y)
    (hm : IsNaturalOrCore τ (MonoidHom.id S))
    (u : S) (A P : Subgroup S) (hAP : A ≤ P)
    (hP : P ≤ borel.map (MulAut.conj u).toMonoidHom)
    [IsElementaryAbelian 2 P] (hne : A ≠ ⊥) :
    (subspaceCommutator τ (fixedSpace τ A) P ≤
      fixedSpace τ (D.map (MulAut.conj u).toMonoidHom)) ∧
    (∀ w ∈ subspaceCommutator τ (fixedSpace τ A) P,
      (∀ g : S, τ g w=w) → w=0) := by
  let f := (MulAut.conj u⁻¹).toMonoidHom
  let A₀ := A.map f
  let P₀ := P.map f
  have hP₀ : P₀ ≤ borel := by
    rintro _ ⟨g,hg,rfl⟩
    obtain ⟨b,hb,rfl⟩ := hP hg
    have heq : f ((MulAut.conj u).toMonoidHom b)=b := by
      change u⁻¹*(u*b*u⁻¹)*u=b
      group
    rw [heq]
    exact hb
  have hn₀ : A₀ ≠ ⊥ := by
    intro he
    apply hne
    apply (map_injective (f := f) (MulAut.conj u⁻¹).injective)
    exact he.trans (map_bot f).symm
  have hex : ∃ t ∈ A₀, t ≠ 1 := by
    by_contra hn
    apply hn₀
    apply le_bot_iff.mp
    intro t ht
    exact Classical.byContradiction (fun ht1 => hn ⟨t,ht,ht1⟩)
  obtain ⟨t,ht,htn⟩ := hex
  let : IsElementaryAbelian 2 P₀ := IsElementaryAbelian.map f
  have htP : t ∈ P₀ := map_mono hAP ht
  have hc (g : S) (hg : g ∈ P₀) : Commute t g := by
    exact congrArg Subtype.val (mul_comm (⟨t,htP⟩ : P₀) ⟨g,hg⟩)
  have hh := cover_kernel τ hm t (hP₀ htP) htn
    (elemPow_eq_one_of_isElementaryAbelian t htP) P₀ hP₀
    (fun g hg => elemPow_eq_one_of_isElementaryAbelian g hg) hc
  have he (g : S) (v : Y) : τ u⁻¹ (τ g v)=τ (f g) (τ u⁻¹ v) := by
    change τ u⁻¹ (τ g v)=τ (u⁻¹*g*u) (τ u⁻¹ v)
    simp only [map_mul,Module.End.mul_apply,τ.self_inv_apply]
  have hfixed (v : Y) (hv : v ∈ fixedSpace τ A) :
      τ u⁻¹ v ∈ fixedSpace τ (zpowers t) := by
    apply (mem_fixedSpace_zpowers_iff _ _ _).mpr
    obtain ⟨a,ha,rfl⟩ := ht
    rw [←he]
    exact congrArg (τ u⁻¹) (hv ⟨a,ha⟩)
  have hmove : (subspaceCommutator τ (fixedSpace τ A) P).map (τ u⁻¹) ≤
      subspaceCommutator τ (fixedSpace τ (zpowers t)) P₀ := by
    rw [Submodule.map_le_iff_le_comap]
    apply Submodule.span_le.mpr
    rintro _ ⟨g,hg,v,hv,rfl⟩
    change τ u⁻¹ (τ g v-v) ∈ subspaceCommutator τ (fixedSpace τ (zpowers t)) P₀
    rw [map_sub,he]
    exact Submodule.subset_span ⟨f g,mem_map_of_mem f hg,τ u⁻¹ v,hfixed v hv,rfl⟩
  constructor
  · intro w hw j
    obtain ⟨d,hd,heq⟩ := j.property
    have hj : f j.val=d := by
      rw [←heq]
      change u⁻¹*(u*d*u⁻¹)*u=d
      group
    apply (τ.apply_bijective u⁻¹).injective
    change τ u⁻¹ (τ j.val w)=τ u⁻¹ w
    rw [he,hj]
    exact hh.1 (hmove ⟨w,hw,rfl⟩) ⟨d,hd⟩
  · intro w hw hf
    have hzero := hh.2 (τ u⁻¹ w) (hmove ⟨w,hw,rfl⟩)
      (fun g => by rw [hf u⁻¹,hf g])
    rwa [hf u⁻¹] at hzero

end BinaryPermutation.SixCover.BorelKernel
