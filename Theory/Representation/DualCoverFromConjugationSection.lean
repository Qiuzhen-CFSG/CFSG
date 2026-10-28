module
public import Theory.Representation.FirstCohomologyDuality
public import Theory.ElementaryAbelian.VectorSpace


/-!
# Dual covers from literal conjugation sections

A surjective central-cover projection and a conjugation-section projection with
the same kernel induce an injective map from the natural quotient into the
section. When all section displacements come from the original moving group
and the section has no fixed vectors, this inclusion is a dual cover. Its image
is exactly the image of that moving group under the original coordinate map.

Source application: MS93 (3.4), printed p.869, before applying (1.5)(ii) to the dual.
-/

public noncomputable section
open Subgroup Representation Representation.OneCohomology
open scoped IsMulCommutative commutatorElement
namespace Representation.OneCohomology
variable {G D V W T : Type*} [Group G] [Group D]
  [AddCommGroup V] [Module (ZMod 2) V]
  [AddCommGroup W] [Module (ZMod 2) W]
  [AddCommGroup T] [Module (ZMod 2) T]

/-- A fixed-free section whose displacement is the image of a central cover
is a dual cover of that same natural quotient. The original projection is retained. -/
theorem exists_dualCover_of_conjugation_section
    (A U L : Subgroup G) (hUA : U ≤ A) (hLA : L ≤ normalizer (A : Set G))
    (hcomm : ⁅A,L⁆ ≤ U)
    (ρ : Representation (ZMod 2) D V) (σ : Representation (ZMod 2) D W)
    (τ : Representation (ZMod 2) D T)
    (p : ρ.IntertwiningMap τ) (hp : Function.Surjective p)
    (j : Multiplicative V →* G) (hjU : j.range = U)
    (π : A →* Multiplicative W) (hπ : Function.Surjective π)
    (f : L →* D) (hf : Function.Surjective f)
    (hj : ∀ (l : L) (v : V), j (Multiplicative.ofAdd (ρ (f l) v)) =
      (l:G)*j (Multiplicative.ofAdd v)*(l:G)⁻¹)
    (hact : ∀ (l : L) (a : A),
      (π ⟨(l:G)*a*(l:G)⁻¹,
        (mem_normalizer_iff.mp (hLA l.property) a).mp a.property⟩).toAdd =
          σ (f l) (π a).toAdd)
    (hker : ∀ v : V, p v = 0 ↔
      π ⟨j (Multiplicative.ofAdd v),hUA (hjU ▸ ⟨Multiplicative.ofAdd v,rfl⟩)⟩ = 1)
    (hfixed : fixed σ = ⊥) :
    ∃ i : τ.IntertwiningMap σ, Function.Injective i ∧ IsDualCover i.range ∧
      (∀ v : V, i (p v) =
        (π ⟨j (Multiplicative.ofAdd v),hUA (hjU ▸ ⟨Multiplicative.ofAdd v,rfl⟩)⟩).toAdd) ∧
      ∀ w, w ∈ i.toLinearMap.range ↔ ∃ a : A, (a : G) ∈ U ∧ (π a).toAdd = w := by
  let jA := j.codRestrict A (fun v => hUA (hjU ▸ ⟨v,rfl⟩))
  let t : V →ₗ[ZMod 2] W :=
    (AddMonoidHom.toMultiplicative.symm (π.comp jA)).toZModLinearMap 2
  have ht (v : V) : t v = (π (jA (Multiplicative.ofAdd v))).toAdd := rfl
  have htker : p.toLinearMap.ker = t.ker := by
    ext v
    exact hker v
  let e := p.toLinearMap.quotKerEquivOfSurjective hp
  let b := p.toLinearMap.ker.liftQ t htker.le
  let i := b.comp e.symm.toLinearMap
  have hi (v : V) : i (p v) = t v := by
    change b (e.symm (e (p.toLinearMap.ker.mkQ v))) = t v
    rw [e.symm_apply_apply]
    rfl
  have htact (g : D) (v : V) : t (ρ g v) = σ g (t v) := by
    obtain ⟨l,rfl⟩ := hf g
    rw [ht,ht]
    have he : jA (Multiplicative.ofAdd (ρ (f l) v)) =
      ⟨(l:G)*(jA (Multiplicative.ofAdd v):G)*(l:G)⁻¹,
        (mem_normalizer_iff.mp (hLA l.property) _).mp (jA (Multiplicative.ofAdd v)).property⟩ :=
      Subtype.ext (hj l v)
    rw [he]
    exact hact l _
  let ii : τ.IntertwiningMap σ := i.intertwiningMap_of_isIntertwiningMap _ _ (by
    intro g x
    obtain ⟨v,rfl⟩ := hp x
    rw [←p.isIntertwining,hi,hi,htact])
  have hii : Function.Injective ii := by
    have hb : Function.Injective b := LinearMap.ker_eq_bot.mp
      (Submodule.ker_liftQ_eq_bot p.toLinearMap.ker t htker.le htker.ge)
    exact hb.comp e.symm.injective
  have hrange (w : W) : w ∈ ii.toLinearMap.range ↔ ∃ a : A, (a : G) ∈ U ∧ (π a).toAdd = w := by
    constructor
    · rintro ⟨v,rfl⟩
      obtain ⟨x,rfl⟩ := hp v
      refine ⟨jA (Multiplicative.ofAdd x),hjU ▸ ⟨Multiplicative.ofAdd x,rfl⟩,?_⟩
      exact (hi x).symm
    · rintro ⟨a,ha,hav⟩
      obtain ⟨x,hx⟩ := (hjU.symm ▸ ha : (a : G) ∈ j.range)
      refine ⟨p x.toAdd,?_⟩
      change i (p x.toAdd) = w
      rw [hi,ht]
      have hxa : jA x = a := Subtype.ext hx
      change (π (jA x)).toAdd = w
      rw [hxa]
      exact hav
  refine ⟨ii,hii,⟨?_,hfixed⟩,hi,hrange⟩
  intro g w
  obtain ⟨l,rfl⟩ := hf g
  obtain ⟨a,ha⟩ := hπ (Multiplicative.ofAdd w)
  have haw : (π a).toAdd = w := congrArg Multiplicative.toAdd ha
  let c : A := ⟨(l:G)*a*(l:G)⁻¹,
    (mem_normalizer_iff.mp (hLA l.property) a).mp a.property⟩
  have hcu : ((c*a⁻¹ : A) : G) ∈ U := by
    apply hcomm
    rw [commutator_comm]
    exact commutator_mem_commutator l.property a.property
  obtain ⟨v,hv⟩ := (hjU.symm ▸ hcu : ((c*a⁻¹ : A) : G) ∈ j.range)
  refine ⟨p v.toAdd,?_⟩
  change i (p v.toAdd) = σ (f l) w-w
  rw [hi,ht]
  have hva : jA v = c*a⁻¹ := Subtype.ext hv
  change (π (jA v)).toAdd = _
  rw [hva,map_mul,map_inv]
  simp only [toAdd_mul,toAdd_inv]
  rw [←sub_eq_add_neg,hact,haw]

end Representation.OneCohomology
