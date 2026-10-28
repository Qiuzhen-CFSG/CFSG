module

public import Theory.SpecificGroups.PSL3.FullTorusGraphEscape
public import Theory.GroupTheory.CyclicHallNormalizerEscape

/-!
# Aligning prescribed subgroups for graph escape

The full projective torus has two-power relative index in the Borel; this
index is unchanged by preimage under a surjection. Sylow conjugacy therefore
puts any odd-primary subgroup of a scalar-cover Borel into the full torus.
Conjugating the compatible pair of automorphisms at the same time preserves
both its nontrivial diagram action and the upper unipotent subgroup.
The full-torus graph theorem then gives escape for the original subgroup.

Source: Aschbacher--Smith 4.4.13(1), printed pp.623--624.
-/


public section
open Subgroup
open scoped MatrixGroups
open Matrix.PSL3 Matrix.PSL3.LinearThree Matrix.PSL3.CartanActions
namespace Matrix.PSL3.FullTorusGraphEscape
variable {F : Type*} [Field F] [Finite F]
theorem torus_relativeIndex_twoPower {n : ℕ} (hF : Nat.card F = 2^n) :
    (torus F).relIndex (borel F) = 2^(n*3) := by
  change ((torus F).subgroupOf (borel F)).index = _
  rw [(BorelQuotient.borel_complement F hF).index_eq_card,
    Nat.card_congr (subgroupOfEquivOfLe (unipotent_le_borel F)).toEquiv,
    card_unipotent,hF,pow_mul]

variable {L : Type*} [Group L] [Finite L]
theorem exists_conj_le_fullTorus_preimage {n : ℕ} (hF : Nat.card F = 2^n)
    (r : L →* PSL(3,F)) (hr : Function.Surjective r)
    {p : ℕ} [Fact p.Prime] (hp : Odd p) (A : Subgroup L)
    (hA : IsPGroup p A) (hAB : A ≤ (borel F).comap r) :
    ∃ g : (borel F).comap r,
      A.map (MulAut.conj (g : L)).toMonoidHom ≤ (torus F).comap r := by
  have hindex : ¬ p ∣ (((torus F).comap r).subgroupOf ((borel F).comap r)).index := by
    change ¬ p ∣ ((torus F).comap r).relIndex ((borel F).comap r)
    rw [relIndex_comap,map_comap_eq_self_of_surjective hr,torus_relativeIndex_twoPower hF]
    exact fun hd => (Fact.out : p.Prime).ne_one
      (Nat.eq_one_of_dvd_coprimes (hp.coprime_two_right.pow_right _) (dvd_refl p) hd)
  obtain ⟨g,hg⟩ := Theory.GroupTheory.exists_conj_le_of_prime_not_dvd_index
    (((torus F).comap r).subgroupOf ((borel F).comap r))
    (A.subgroupOf ((borel F).comap r)) hindex hA.comap_subtype
  refine ⟨g,?_⟩
  rintro _ ⟨a,ha,rfl⟩
  exact hg ⟨⟨a,hAB ha⟩,ha,rfl⟩
omit [Finite L] in
private theorem conjugate_actor (r : L →* PSL(3,F))
    (α : MulAut L) (β : MulAut PSL(3,F))
    (hcomp : r.comp α.toMonoidHom = β.toMonoidHom.comp r)
    (A : Subgroup L) (hA : A.map α.toMonoidHom = A)
    (hU : (unipotent F).map β.toMonoidHom = unipotent F)
    (hout : β ∉ ExtensionBorel.linearField F)
    (g : (borel F).comap r) :
    let α' := MulAut.conj (g : L) * α * (MulAut.conj (g : L))⁻¹
    let β' := MulAut.conj (r g) * β * (MulAut.conj (r g))⁻¹
    r.comp α'.toMonoidHom = β'.toMonoidHom.comp r ∧
    (A.map (MulAut.conj (g : L)).toMonoidHom).map α'.toMonoidHom =
      A.map (MulAut.conj (g : L)).toMonoidHom ∧
    (unipotent F).map β'.toMonoidHom = unipotent F ∧
    β' ∉ ExtensionBorel.linearField F := by
  dsimp only
  refine ⟨?_,?_,?_,?_⟩
  · apply MonoidHom.ext
    intro x
    change r ((g : L) * α ((g : L)⁻¹ * x * g) * (g : L)⁻¹) =
      r g * β ((r g)⁻¹ * r x * r g) * (r g)⁻¹
    have hc (x : L) : r (α x) = β (r x) := DFunLike.congr_fun hcomp x
    rw [map_mul,map_mul,map_inv,hc]
    simp only [map_mul,map_inv]
  · rw [Subgroup.map_map]
    have he : (MulAut.conj (g : L) * α * (MulAut.conj (g : L))⁻¹).toMonoidHom.comp
        (MulAut.conj (g : L)).toMonoidHom =
        (MulAut.conj (g : L)).toMonoidHom.comp α.toMonoidHom := by
      ext x
      simp
      group
    rw [he,←Subgroup.map_map,hA]
  · have hg : r g ∈ normalizer (unipotent F : Set PSL(3,F)) :=
      borel_le_normalizer_unipotent F g.property
    have hgmap := mem_normalizer_iff_map_conj_eq.mp hg
    have hgimap := mem_normalizer_iff_map_conj_eq.mp ((normalizer _).inv_mem hg)
    have he : (MulAut.conj (r g) * β * (MulAut.conj (r g))⁻¹).toMonoidHom =
        (MulAut.conj (r g)).toMonoidHom.comp
          (β.toMonoidHom.comp (MulAut.conj (r g)⁻¹).toMonoidHom) := by
      rw [← map_inv MulAut.conj (r g)]
      rfl
    rw [he,←Subgroup.map_map,←Subgroup.map_map]
    have hi : (unipotent F).map (MulAut.conj (r g)⁻¹).toMonoidHom = unipotent F := hgimap
    have hf : (unipotent F).map (MulAut.conj (r g)).toMonoidHom = unipotent F := hgmap
    rw [hi,hU,hf]
  · have hi : MulAut.conj (r g) ∈ ExtensionBorel.linearField F :=
      (show OuterSolvable.innerDiagonal F ≤ ExtensionBorel.linearField F from le_sup_left)
        (OuterSolvable.inner_le_innerDiagonal F ⟨r g,rfl⟩)
    intro h
    apply hout
    have hh := (ExtensionBorel.linearField F).mul_mem
      ((ExtensionBorel.linearField F).mul_mem ((ExtensionBorel.linearField F).inv_mem hi) h) hi
    have he : (MulAut.conj (r g))⁻¹ *
        (MulAut.conj (r g) * β * (MulAut.conj (r g))⁻¹) * MulAut.conj (r g) = β := by group
    rwa [he] at hh

/-- A compatible graph actor stabilizing an odd-primary subgroup of the actual
Borel preimage forces escape for that prescribed subgroup. -/
theorem normalizer_escape_of_borel_graph_stable [CharP F 2] {n : ℕ}
    (hn : 1 < n) (hF : Nat.card F = 2^n)
    (r : L →* PSL(3,F)) (hr : Function.Surjective r)
    (k : SL(3,F) →* L) (hk : Function.Surjective k)
    (hfac : r.comp k = projection F)
    (α : MulAut L) (β : MulAut PSL(3,F))
    (hcomm : ∀ x, r (α x) = β (r x))
    (hU : (unipotent F).map β.toMonoidHom = unipotent F)
    (hmove : β ∉ ExtensionBorel.linearField F)
    {p : ℕ} [Fact p.Prime] (hp : Odd p)
    (A : Subgroup L) (hA : IsPGroup p A) (hAB : A ≤ (borel F).comap r)
    (hstable : A.map α.toMonoidHom = A) :
    ¬ normalizer (A : Set L) ≤ (borel F).comap r := by
  obtain ⟨g,hg⟩ := exists_conj_le_fullTorus_preimage hF r hr hp A hA hAB
  obtain ⟨hcomp,hst,hun,hout⟩ := conjugate_actor r α β (MonoidHom.ext hcomm)
    A hstable hU hmove g
  have hesc := normalizer_escape_of_graph_stable F hn hF r k hk hfac
    (MulAut.conj (g : L) * α * (MulAut.conj (g : L))⁻¹)
    (MulAut.conj (r g) * β * (MulAut.conj (r g))⁻¹)
    (fun x => DFunLike.congr_fun hcomp x) hun hout
    (A.map (MulAut.conj (g : L)).toMonoidHom) hg hst
  intro hN
  apply hesc
  rw [← map_equiv_normalizer_eq]
  rintro _ ⟨x,hx,rfl⟩
  exact ((borel F).comap r).mul_mem
    (((borel F).comap r).mul_mem g.property (hN hx))
    (((borel F).comap r).inv_mem g.property)

end Matrix.PSL3.FullTorusGraphEscape
