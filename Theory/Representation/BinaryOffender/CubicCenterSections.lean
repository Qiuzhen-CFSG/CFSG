module

public import Theory.Representation.BinaryOffender.QuasisimpleCentralSection
public import Theory.Representation.BinaryOffender.AmbientSectionTransport

/-!
# Faithful irreducible sections detecting a cubic center

A faithful binary action of a quasisimple group with center of order three
has an Irr⁺ section on which the group acts faithfully. For a nonidentity
central element z, the kernel of z² + z + 1 is nonzero, invariant, and has
no nonzero z-fixed vectors. Choose an Irr⁺ section in this subspace. Its
kernel is central; prime order of the center and the choice of subspace
force that kernel to be trivial.

The transport lemmas preserve faithfulness on the literal central quotient
through an equivariant subspace embedding and a change of ambient group.
They supply the extra faithfulness assertion in the use of B.1.11 in
Aschbacher–Smith, *The Classification of Quasithin Groups*, B.1.13,
printed pp. 73–74 (PDF pp. 84–85), combined manuscript of 1 March 2004.
-/

public section
open Subgroup Theory.GroupTheory
namespace Representation.BinaryOffender
variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V] (ρ : Representation (ZMod 2) G V)

omit [FiniteDimensional (ZMod 2) V] in
private theorem add_self (v : V) : v + v = 0 := by
  simpa only [show (1 : ZMod 2) + 1 = 0 by decide, zero_smul, one_smul]
    using (add_smul (1 : ZMod 2) 1 v).symm

/-- A section detecting the cubic center, constructed without a
semisimplicity or section-existence assumption. -/
theorem exists_faithful_isIrrPlus_of_cubic_center (L : Subgroup G) [IsQuasisimple L]
    (hf : Function.Injective (ρ.comp L.subtype)) (hc : Nat.card (center L) = 3) :
    ∃ I, ∃ hI : IsIrrPlus ρ L I,
      Function.Injective (centralQuotientRepresentation ρ L I hI.choose) := by
  classical
  have hn : Nontrivial (center L) := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  let := hn
  obtain ⟨z, hz⟩ := exists_ne (1 : center L)
  have hz3 : (z : L) ^ 3 = 1 := by
    have h : z ^ 3 = 1 := hc ▸ pow_card_eq_one'
    exact congrArg Subtype.val h
  have hzG3 : ((z : L) : G) ^ 3 = 1 := congrArg Subtype.val hz3
  have hcomm (g : L) (v : V) : ρ (z : L) (ρ g v) = ρ g (ρ (z : L) v) := by
    rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
    exact congrArg (fun x : L => ρ (x : G) v) ((mem_center_iff.mp z.property g).symm)
  let t := ρ ((z : L) : G)
  let W : Submodule (ZMod 2) V := (t * t + t + 1).ker
  have hW : L ≤ subspaceStabilizer ρ W := by
    apply le_subspaceStabilizer
    intro g hg v hv
    change t (t (ρ g v)) + t (ρ g v) + ρ g v = 0
    change t (t v) + t v + v = 0 at hv
    simpa only [t, hcomm ⟨g, hg⟩, ← map_add, hv, map_zero] using congrArg (ρ g) hv
  have hzero (v : V) (hv : v ∈ W) (hfix : t v = v) : v = 0 := by
    change t (t v) + t v + v = 0 at hv
    simpa only [hfix, add_self, zero_add] using hv
  have hWne : W ≠ ⊥ := by
    intro he
    apply hz
    apply Subtype.ext
    apply hf
    ext v
    have hm : t v - v ∈ W := by
      change t (t (t v - v)) + t (t v - v) + (t v - v) = 0
      have hcube : t (t (t v)) = v := by
        change (ρ _ * ρ _ * ρ _) v = v
        rw [← map_mul, ← map_mul, show ((z : L) : G) * z * z = ((z : L) : G)^3 by simp [pow_succ], hzG3, map_one]
        rfl
      simp only [map_sub, hcube]
      abel
    have hzv : t v - v = 0 := by simpa only [he, Submodule.mem_bot] using hm
    simpa only [t, MonoidHom.comp_apply, Subgroup.subtype_apply, Subgroup.coe_one, map_one, Module.End.one_apply] using sub_eq_zero.mp hzv
  let σ := (invariantSubspace ρ L W hW).toRepresentation
  have hnot : ¬ (⊤ : Submodule (ZMod 2) W) ≤ fixedSpace σ ⊤ := by
    intro h
    apply hWne
    apply le_bot_iff.mp
    intro v hv
    exact hzero v hv (congrArg Subtype.val (h (Submodule.mem_top : (⟨v,hv⟩ : W) ∈ ⊤) ⟨z, mem_top _⟩))
  obtain ⟨I₀, hI₀⟩ := exists_isIrrPlus_of_not_fixed σ (⊤ : Subgroup L) hnot
  let I := I₀.map W.subtype
  have hi : IsIrrPlus (ρ.comp L.subtype) (⊤ : Subgroup L) I := by
    apply IsIrrPlus.map_embedding (ρ.comp L.subtype) σ (MonoidHom.id L)
      W.subtype W.subtype_injective (fun _ _ => rfl) ⊤ I₀
    simpa only [Subgroup.map_id] using hI₀
  have hI : IsIrrPlus ρ L I := by
    apply (IsIrrPlus.subgroupOf_iff ρ L L le_rfl I).mp
    simpa only [subgroupOf_self] using hi
  have hIW : I ≤ W := Submodule.map_subtype_le _ _
  let τ := centralQuotientRepresentation ρ L I hI.choose
  have hk : τ.ker ≤ center L := by
    intro l hl
    have h := centralSection_kernel_le_centralizer ρ L L le_rfl I hI hI.choose L.le_normalizer
    have hcent := (h (mem_map_of_mem L.subtype hl)).2
    exact mem_center_iff.mpr (fun x => Subtype.ext ((mem_centralizer_iff.mp hcent) x x.property))
  have hznot : (z : L) ∉ τ.ker := by
    intro hzker
    apply hI.ne_bot ρ
    apply le_bot_iff.mp
    intro v hv
    have hfix := (centralSectionRepresentation_ker_iff ρ L L I hI.choose L.le_normalizer z).mp hzker v hv
    have hdW : t v - v ∈ W := W.sub_mem ((hW z.val.property v).2 (hIW hv)) (hIW hv)
    have hd : t v - v = 0 := hzero _ hdW (hfix z)
    exact hzero v (hIW hv) (sub_eq_zero.mp hd)
  refine ⟨I, hI, (injective_iff_map_eq_one τ).mpr ?_⟩
  intro x hx
  by_contra hxne
  let K := τ.ker.subgroupOf (center L)
  have hKne : K ≠ ⊥ := by
    intro he
    have hm : (⟨x, hk hx⟩ : center L) ∈ K := hx
    have heq : (⟨x, hk hx⟩ : center L) = 1 := by simpa only [he, Subgroup.mem_bot] using hm
    exact hxne (congrArg Subtype.val heq)
  let : Fact (Nat.card (center L)).Prime := ⟨hc ▸ Nat.prime_three⟩
  have hK : K = ⊤ := K.eq_bot_or_eq_top_of_prime_card.resolve_left hKne
  exact hznot (show z ∈ K from hK.symm ▸ mem_top z)

variable {G D V W : Type*} [Group G] [Group D]
  [AddCommGroup V] [Module (ZMod 2) V] [AddCommGroup W] [Module (ZMod 2) W]
  (ρ : Representation (ZMod 2) G V) (σ : Representation (ZMod 2) D W)

/-- Faithfulness survives an equivariant embedding when the map of the
acting subgroup is injective. Both representations use their actual
quotients by fixed vectors. -/
theorem centralQuotientRepresentation_injective_map_embedding (f : G →* D) (e : W →ₗ[ZMod 2] V)
    (he : Function.Injective e) (hact : ∀ g w, ρ g (e w) = e (σ (f g) w))
    (L : Subgroup G) (hf : Function.Injective (f.subgroupMap L))
    (I : Submodule (ZMod 2) W) (hI : L.map f ≤ subspaceStabilizer σ I)
    (hfaith : Function.Injective (centralQuotientRepresentation σ (L.map f) I hI)) :
    Function.Injective (centralQuotientRepresentation ρ L (I.map e)
      (map_subspace_invariant ρ σ f e hact L I hI)) := by
  intro x y hxy
  apply hf
  apply hfaith
  apply LinearMap.ext
  intro v
  apply (embeddedCentralQuotientEquiv ρ σ f e he hact L I).injective
  rw [embeddedCentralQuotientEquiv_intertwines ρ σ f e he hact L I hI,
    embeddedCentralQuotientEquiv_intertwines ρ σ f e he hact L I hI, hxy]

/-- Faithfulness on the central quotient is unchanged when an actor
inside a subgroup is viewed in the original ambient group. -/
theorem centralQuotientRepresentation_injective_to_ambient (L K : Subgroup G) (hLK : L ≤ K)
    (I : Submodule (ZMod 2) V) (hI : IsIrrPlus (ρ.comp K.subtype) (L.subgroupOf K) I)
    (hf : Function.Injective (centralQuotientRepresentation (ρ.comp K.subtype)
      (L.subgroupOf K) I hI.choose)) :
    Function.Injective (centralQuotientRepresentation ρ L I
      ((IsIrrPlus.subgroupOf_iff ρ L K hLK I).mp hI).choose) := by
  apply (injective_iff_map_eq_one _).mpr
  intro l hl
  let l₀ : L.subgroupOf K := ⟨⟨l,hLK l.property⟩,l.property⟩
  have hl₀ : centralQuotientRepresentation (ρ.comp K.subtype) (L.subgroupOf K) I hI.choose l₀ = 1 := by
    apply (centralSectionRepresentation_ker_iff (ρ.comp K.subtype) (L.subgroupOf K)
      (L.subgroupOf K) I hI.choose (L.subgroupOf K).le_normalizer l₀).mpr
    intro v hv
    rw [fixedSpace_subgroupOf ρ L K hLK]
    exact (centralSectionRepresentation_ker_iff ρ L L I
      ((IsIrrPlus.subgroupOf_iff ρ L K hLK I).mp hI).choose L.le_normalizer l).mp hl v hv
  have he : l₀ = 1 := hf (hl₀.trans (map_one _).symm)
  exact Subtype.ext (congrArg (fun x : L.subgroupOf K => ((x : K) : G)) he)

end Representation.BinaryOffender
