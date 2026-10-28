module

public import Theory.Representation.BinaryConjugationSection.QuadraticPair
public import Theory.Representation.FirstCohomology
public import Theory.GroupTheory.CommutatorPreimage
public import Mathlib.RepresentationTheory.Irreducible
import Mathlib.Tactic.Group
import Mathlib.Tactic.Abel

/-!
# Fixed-preimage splitting of an actual binary section

Commutators of elements of Q with L give crossed homomorphisms in the
specified coordinates on S/V. If these vanish on the kernel of the marked
actor map, they descend to that same actor. Vanishing first cohomology then
corrects each element of Q by an element of S. No elementary-abelian or
commutative structure on Q/V is presumed. A fixed-point-free section gives
the exact intersection, and the literal quotient images multiply as a direct
product. The irreducible-section lemma supplies the group-theoretic bridge
needed to verify kernel vanishing using the p-core.

Application: Aschbacher--Smith, 14.7.74, printed p.1077 (PDF p.1094),
combined manuscript of 1 March 2004.
-/

@[expose] public section

open Subgroup Representation
open scoped commutatorElement
noncomputable section

namespace Representation.OneCohomology
variable {k A B M : Type*} [CommRing k] [Group A] [Group B]
  [AddCommGroup M] [Module k M]

/-- A cocycle vanishing on the kernel descends through the specified actor map. -/
theorem principal_of_surjective (ρ : Representation k B M)
    [Subsingleton (H1 ρ)] (π : A →* B) (hπ : Function.Surjective π)
    (c : cocycles (ρ.comp π)) (hker : ∀ a ∈ π.ker, c.val a = 0) :
    ∃ w : M, ∀ a : A, c.val a = ρ (π a) w - w := by
  have hfiber (a b : A) (h : π a = π b) : c.val a = c.val b := by
    have hk : a⁻¹ * b ∈ π.ker := by
      apply MonoidHom.mem_ker.mpr
      rw [map_mul, map_inv, h, inv_mul_cancel]
    have he := c.property a (a⁻¹ * b)
    rw [mul_inv_cancel_left, hker _ hk, map_zero, zero_add] at he
    exact he.symm
  let s := Function.surjInv hπ
  have hs (b : B) : π (s b) = b := Function.rightInverse_surjInv hπ b
  let c' : cocycles ρ := ⟨fun b => c.val (s b), by
    intro b t
    change c.val (s (b * t)) = ρ b (c.val (s t)) + c.val (s b)
    rw [hfiber (s (b * t)) (s b * s t) (by rw [hs, map_mul, hs, hs])]
    simpa only [MonoidHom.comp_apply, hs] using c.property (s b) (s t)⟩
  obtain ⟨w, hw⟩ := (classMap_eq_zero_iff ρ c').mp (Subsingleton.elim _ _)
  refine ⟨w, fun a => ?_⟩
  have he := congrArg (fun f : cocycles ρ => f.val (π a)) hw
  change ρ (π a) w - w = c.val (s (π a)) at he
  exact (hfiber a (s (π a)) (hs (π a)).symm).trans he.symm
end Representation.OneCohomology

namespace Representation.BinaryConjugationSection
variable {G D W : Type*} [Group G] [Group D] [AddCommGroup W] [Module (ZMod 2) W]
  {L S V : Subgroup G} {ρ : Representation (ZMod 2) D W}
  (π : L →* D) (d : BinaryConjugationSection L S V (ρ.comp π))
  (Q : Subgroup G) (hc : ⁅L,Q⁆ ≤ S)

/-- The displacement of an original group element in the actual section coordinates. -/
def commutatorCocycle (x : Q) : OneCohomology.cocycles (ρ.comp π) :=
  ⟨fun l => (d.coordinates ⟨⁅(l : G), (x : G)⁆,
    hc (commutator_mem_commutator l.property x.property)⟩).toAdd, by
    intro l m
    let cm : S := ⟨⁅(m : G), (x : G)⁆,
      hc (commutator_mem_commutator m.property x.property)⟩
    let cl : S := ⟨⁅(l : G), (x : G)⁆,
      hc (commutator_mem_commutator l.property x.property)⟩
    let conj : S := ⟨l * cm * (l : G)⁻¹,
      (mem_normalizer_iff.mp (d.normalized l.property) cm).mp cm.property⟩
    have he : (⟨⁅((l * m : L) : G), (x : G)⁆,
        hc (commutator_mem_commutator (l * m).property x.property)⟩ : S) = conj * cl := by
      apply Subtype.ext
      exact commutatorElement_mul_left_eq_conj_mul _ _ _
    change (d.coordinates _).toAdd = _
    rw [he, map_mul]
    change (d.coordinates conj).toAdd + (d.coordinates cl).toAdd = _
    rw [d.equivariant]⟩

end Representation.BinaryConjugationSection

namespace Representation.BinaryConjugationSection
variable {G D W : Type*} [Group G] [Group D] [AddCommGroup W] [Module (ZMod 2) W]
  {L S V : Subgroup G} {ρ : Representation (ZMod 2) D W}

/-- Vanishing H¹ corrects each original group element by an element of S.
Only S/V is linearized; Q/V is not assumed abelian or elementary. -/
theorem exists_fixed_mod_kernel [Subsingleton (OneCohomology.H1 ρ)]
    (π : L →* D) (hπ : Function.Surjective π)
    (d : BinaryConjugationSection L S V (ρ.comp π))
    (Q : Subgroup G) (hc : ⁅L,Q⁆ ≤ S)
    (hk : ∀ l ∈ π.ker, ∀ x ∈ Q, ⁅(l : G), x⁆ ∈ V) (x : Q) :
    ∃ s : S, ∀ l : L, ⁅(l : G), (s : G)⁻¹ * x⁆ ∈ V := by
  let c := d.commutatorCocycle π Q hc x
  have hker (l : L) (hl : l ∈ π.ker) : c.val l = 0 := by
    exact congrArg Multiplicative.toAdd
      ((d.coordinates_eq_one_iff _).mpr (hk l hl x x.property))
  obtain ⟨w, hw⟩ := OneCohomology.principal_of_surjective ρ π hπ c hker
  obtain ⟨s, hs⟩ := d.onto (Multiplicative.ofAdd w)
  refine ⟨s, fun l => ?_⟩
  let cx : S := ⟨⁅(l : G), (x : G)⁆,
    hc (commutator_mem_commutator l.property x.property)⟩
  let cs : S := ⟨l * s * (l : G)⁻¹,
    (mem_normalizer_iff.mp (d.normalized l.property) s).mp s.property⟩
  let y : S := cs⁻¹ * cx * s
  have hy : (y : G) = ⁅(l : G), (s : G)⁻¹ * x⁆ := by
    change ((l : G) * s * (l : G)⁻¹)⁻¹ * ⁅(l : G), (x : G)⁆ * s = _
    simp only [commutatorElement_def]
    group
  rw [← hy]
  apply (d.coordinates_eq_one_iff y).mp
  apply Multiplicative.toAdd.injective
  change (d.coordinates (cs⁻¹ * cx * s)).toAdd = 0
  simp only [d.coordinates.map_mul, d.coordinates.map_inv]
  change -(d.coordinates cs).toAdd + (d.coordinates cx).toAdd +
    (d.coordinates s).toAdd = 0
  rw [d.equivariant, hs]
  change -ρ (π l) w + c.val l + w = 0
  rw [hw]
  abel
end Representation.BinaryConjugationSection

open Subgroup Representation
open scoped commutatorElement
noncomputable section
namespace Representation.BinaryConjugationSection
variable {G W : Type*} [Group G] [AddCommGroup W] [Module (ZMod 2) W]
  {L S V : Subgroup G} {ρ : Representation (ZMod 2) L W}

/-- Irreducibility of the marked action is irreducibility of the original group section. -/
theorem eq_kernel_or_section [IsIrreducible ρ]
    (d : BinaryConjugationSection L S V ρ)
    (E : Subgroup G) (hVE : V ≤ E) (hES : E ≤ S)
    (hLE : L ≤ normalizer (E : Set G)) : E = V ∨ E = S := by
  let M : Subrepresentation ρ := {
    toSubmodule := d.imageSpace E
    apply_mem_toSubmodule := by
      intro l w hw
      obtain ⟨s, hs, rfl⟩ := (d.mem_imageSpace_iff E w).mp hw
      exact (d.mem_imageSpace_iff E _).mpr
        ⟨⟨l * s * (l : G)⁻¹,
          (mem_normalizer_iff.mp (d.normalized l.property) s).mp s.property⟩,
          (mem_normalizer_iff.mp (hLE l.property) s).mp hs, d.equivariant l s⟩ }
  rcases (inferInstance : IsIrreducible ρ).eq_bot_or_eq_top M with hb | ht
  · left
    apply le_antisymm ?_ hVE
    intro x hx
    let s : S := ⟨x, hES hx⟩
    have hm : (d.coordinates s).toAdd ∈ M :=
      (d.mem_imageSpace_iff E _).mpr ⟨s, hx, rfl⟩
    rw [hb] at hm
    exact (d.coordinates_eq_one_iff s).mp hm
  · right
    apply le_antisymm hES
    intro x hx
    let s : S := ⟨x, hx⟩
    have hm : (d.coordinates s).toAdd ∈ M := by rw [ht]; trivial
    obtain ⟨e, he, hcoord⟩ := (d.mem_imageSpace_iff E _).mp hm
    have hk : (e⁻¹ * s : S).val ∈ V := by
      apply (d.coordinates_eq_one_iff _).mp
      rw [map_mul, map_inv, Multiplicative.toAdd.injective hcoord, inv_mul_cancel]
    have hm := E.mul_mem he (hVE hk)
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_cancel_left] using hm
end Representation.BinaryConjugationSection

namespace Representation.OneCohomology
variable {k D W : Type*} [Field k] [Group D] [Nontrivial D]
  [AddCommGroup W] [Module k W]

theorem fixed_eq_bot_of_faithful_irreducible (ρ : Representation k D W)
    [IsIrreducible ρ] (hρ : Function.Injective ρ) : fixed ρ = ⊥ := by
  let M : Subrepresentation ρ := {
    toSubmodule := fixed ρ
    apply_mem_toSubmodule := by
      intro g w hw
      change ∀ h, ρ h (ρ g w) = ρ g w
      rw [hw g]
      exact hw }
  rcases (inferInstance : IsIrreducible ρ).eq_bot_or_eq_top M with hb | ht
  · exact congrArg Subrepresentation.toSubmodule hb
  · obtain ⟨g, hg⟩ := exists_ne (1 : D)
    apply False.elim (hg (hρ ?_))
    ext w
    have hw : w ∈ M := by rw [ht]; trivial
    exact (hw g).trans (by simp)
end Representation.OneCohomology
namespace Subgroup
variable {G : Type*} [Group G]
open scoped commutatorElement

/-- Elementwise membership in the actual fixed-space preimage. -/
theorem mem_commutatorPreimage_iff (Q L V : Subgroup G)
    (hn : Q ≤ normalizer (V : Set G)) (x : G) :
    x ∈ commutatorPreimage Q L V ↔ x ∈ Q ∧ ∀ l ∈ L, ⁅x,l⁆ ∈ V := by
  constructor
  · intro hx
    exact ⟨commutatorPreimage_le Q L V hx,
      fun l hl => commutator_le.mp (commutator_commutatorPreimage_le Q L V hn) x hx l hl⟩
  · intro hx
    let C : Subgroup G := {
      carrier := {x | x ∈ Q ∧ ∀ l ∈ L, ⁅x,l⁆ ∈ V}
      one_mem' := ⟨Q.one_mem, by simp⟩
      mul_mem' := by
        rintro x y ⟨hx,hxc⟩ ⟨hy,hyc⟩
        refine ⟨Q.mul_mem hx hy, fun l hl => ?_⟩
        rw [commutatorElement_mul_left_eq_conj_mul]
        exact V.mul_mem ((mem_normalizer_iff.mp (hn hx) _).mp (hyc l hl)) (hxc l hl)
      inv_mem' := by
        rintro x ⟨hx,hxc⟩
        refine ⟨Q.inv_mem hx, fun l hl => ?_⟩
        rw [commutatorElement_inv_left]
        have hi : ⁅l,x⁆ ∈ V := by
          rw [← commutatorElement_inv]
          exact V.inv_mem (hxc l hl)
        simpa only [inv_inv] using
          (mem_normalizer_iff.mp (hn (Q.inv_mem hx)) _).mp hi }
    have hC : C ≤ commutatorPreimage Q L V :=
      le_commutatorPreimage (fun _ h => h.1) (commutator_le.mpr fun _ h => h.2)
    exact hC hx
end Subgroup

namespace Representation.BinaryConjugationSection
variable {G D W : Type*} [Group G] [Group D] [AddCommGroup W] [Module (ZMod 2) W]
  {L S V : Subgroup G} {ρ : Representation (ZMod 2) D W}

/-- The cocycle correction yields a splitting by the literal fixed preimage. -/
theorem sup_fixedPreimage_eq [Subsingleton (OneCohomology.H1 ρ)]
    (π : L →* D) (hπ : Function.Surjective π)
    (d : BinaryConjugationSection L S V (ρ.comp π))
    (Q : Subgroup G) (hSQ : S ≤ Q) (hQV : Q ≤ normalizer (V : Set G))
    (hc : ⁅L,Q⁆ ≤ S)
    (hk : ∀ l ∈ π.ker, ∀ x ∈ Q, ⁅(l : G), x⁆ ∈ V) :
    Q = commutatorPreimage Q L V ⊔ S := by
  apply le_antisymm ?_ (sup_le (commutatorPreimage_le _ _ _) hSQ)
  intro x hx
  obtain ⟨s, hs⟩ := d.exists_fixed_mod_kernel π hπ Q hc hk ⟨x,hx⟩
  have hy : (s : G)⁻¹ * x ∈ commutatorPreimage Q L V := by
    apply (mem_commutatorPreimage_iff Q L V hQV _).mpr
    refine ⟨Q.mul_mem (Q.inv_mem (hSQ s.property)) hx, fun l hl => ?_⟩
    rw [← commutatorElement_inv]
    exact V.inv_mem (hs ⟨l,hl⟩)
  have hm := (commutatorPreimage Q L V ⊔ S).mul_mem
    (mem_sup_right s.property) (mem_sup_left hy)
  simpa only [mul_inv_cancel_left] using hm

/-- No fixed vectors in S/V identifies the intersection with the original kernel. -/
theorem inf_fixedPreimage_eq (π : L →* D) (hπ : Function.Surjective π)
    (d : BinaryConjugationSection L S V (ρ.comp π))
    (Q : Subgroup G) (hSQ : S ≤ Q) (hQV : Q ≤ normalizer (V : Set G))
    (hLV : L ≤ normalizer (V : Set G)) (hf : OneCohomology.fixed ρ = ⊥) :
    commutatorPreimage Q L V ⊓ S = V := by
  apply le_antisymm ?_ (le_inf
    (le_commutatorPreimage (d.kernel_le.trans hSQ)
      (le_normalizer_iff_commutator_le_left.mp hLV)) d.kernel_le)
  rintro x ⟨hxc, hxs⟩
  let s : S := ⟨x,hxs⟩
  have hfix : (d.coordinates s).toAdd ∈ OneCohomology.fixed ρ := by
    intro g
    obtain ⟨l,rfl⟩ := hπ g
    let y : S := ⟨l * s * (l : G)⁻¹,
      (mem_normalizer_iff.mp (d.normalized l.property) s).mp s.property⟩
    have hy : (y * s⁻¹ : S).val ∈ V := by
      have h := commutator_le.mp (commutator_commutatorPreimage_le Q L V hQV)
        x hxc l l.property
      change ⁅(l : G), x⁆ ∈ V
      rw [← commutatorElement_inv]
      exact V.inv_mem h
    have he := (d.coordinates_eq_one_iff (y * s⁻¹)).mpr hy
    rw [map_mul, map_inv, mul_inv_eq_one] at he
    exact (d.equivariant l s).symm.trans (congrArg Multiplicative.toAdd he)
  rw [hf] at hfix
  exact (d.coordinates_eq_one_iff s).mp hfix
end Representation.BinaryConjugationSection
namespace Subgroup
variable {A B : Type*} [Group A] [Group B]

/-- The original quotient images form a direct product, with their literal multiplication map. -/
theorem image_directProduct_of_ker_eq_inf (f : A →* B) (hf : Function.Surjective f)
    (C S : Subgroup A) (hgen : C ⊔ S = ⊤) (hk : f.ker = C ⊓ S)
    (hc : ⁅C,S⁆ ≤ f.ker) :
    IsCompl (C.map f) (S.map f) ∧
      ∃ e : C.map f × S.map f ≃* B,
        ∀ c s, e (c,s) = (c : B) * (s : B) := by
  have hdis := disjoint_map_of_ker_eq_inf f C S hk
  have hsup : C.map f ⊔ S.map f = ⊤ := by
    rw [← map_sup, hgen, map_top_of_surjective f hf]
  have hcomm : C.map f ≤ centralizer (S.map f : Set B) := by
    apply commutator_eq_bot_iff_le_centralizer.mp
    rw [← map_commutator]
    exact (map_eq_bot_iff _).mpr hc
  obtain ⟨e,he⟩ := exists_mulEquiv_prod_sup_of_disjoint_of_commuting
    (C.map f) (S.map f) hdis hcomm
  exact ⟨⟨hdis, codisjoint_iff.mpr hsup⟩,
    e.trans ((MulEquiv.subgroupCongr hsup).trans Subgroup.topEquiv), he⟩
end Subgroup

