module

public import Theory.Representation.FirstCohomologyAutomorphism.Subkernel
public import Theory.Representation.BinaryAlternatingNaturalCohomology

/-!
# Centralizer splitting from an actual marked five-module

Suppose a subgroup P fixes the marked binary A₅ module N and displaces L
only inside N. The kernel of the original A₅ action may be larger than N,
but lies in P. Comparing conjugations first makes every P-actor fix that
kernel. Vanishing first cohomology then corrects each actor by an element
of N, giving P = N C_P(L). No order bound or block recognition is used.
-/

public section
open Subgroup
open scoped commutatorElement IsMulCommutative
namespace Subgroup
variable {G : Type*} [Group G]

/-- Full centralizer splitting from displacement into the original marked
module, retaining the possibly larger kernel of the A₅ quotient. -/
theorem eq_module_sup_centralizer_of_marked_alternating_five
    (L P : Subgroup G) (N : Subgroup L) [IsMulCommutative N]
    (f : L →* alternatingGroup (Fin 5)) (hf : Function.Surjective f)
    (e : N ≃* Multiplicative (BinaryPermutation.core (Fin 5)))
    (he : ∀ (l : L) (v : BinaryPermutation.core (Fin 5)),
      (e.symm (Multiplicative.ofAdd
        (BinaryPermutation.coreRepresentation (Fin 5) (f l).val v)) : L) =
        l * (e.symm (Multiplicative.ofAdd v) : L) * l⁻¹)
    (hZ : N ⊓ center L = ⊥)
    (hNP : N.map L.subtype ≤ P) (hkernel : f.ker.map L.subtype ≤ P)
    (hPN : P ≤ normalizer (L : Set G))
    (hfix : P ≤ centralizer (N.map L.subtype : Set G))
    (hdis : ⁅P,L⁆ ≤ N.map L.subtype) :
    P = N.map L.subtype ⊔ (P ⊓ centralizer (L : Set G)) := by
  have hMC : f.ker ≤ centralizer (N : Set L) := by
    intro m hm n hn
    exact Subtype.ext (hfix (hkernel (mem_map_of_mem L.subtype hm))
      n (mem_map_of_mem L.subtype hn))
  have hMN : ⁅f.ker,(⊤ : Subgroup L)⁆ ≤ N := by
    apply commutator_le.mpr
    intro m hm l _
    obtain ⟨n,hn,heq⟩ := hdis (commutator_mem_commutator
      (hkernel (mem_map_of_mem L.subtype hm)) l.property)
    exact (show n = ⁅m,l⁆ from Subtype.ext heq) ▸ hn
  let : Subsingleton (Representation.OneCohomology.H1
      (BinaryPermutation.alternatingCoreRepresentation (Fin 5))) :=
    BinaryPermutation.alternatingCore_subsingleton_H1 (Fin 5) (by simp) (by decide)
  apply le_antisymm ?_ (sup_le hNP inf_le_left)
  intro p hp
  let α := L.normalizerMonoidHom ⟨p,hPN hp⟩
  have hd (l : L) : α l * l⁻¹ ∈ N := by
    obtain ⟨n,hn,heq⟩ := hdis (commutator_mem_commutator hp l.property)
    exact (show n = α l * l⁻¹ from Subtype.ext heq) ▸ hn
  have hn (n : L) (hn : n ∈ N) : α n = n := by
    apply Subtype.ext
    change p * (n : G) * p⁻¹ = n
    rw [←hfix hp n (mem_map_of_mem L.subtype hn),mul_inv_cancel_right]
  have hk := Representation.OneCohomology.automorphism_fixes_centralizing_layer
    N f.ker hMC hMN hZ α hd hn
  obtain ⟨n,hn⟩ := Representation.OneCohomology.automorphism_inner_of_H1_zero_of_subkernel
    N f hf e (BinaryPermutation.alternatingCoreRepresentation (Fin 5)) he α hd hk
  have hnG : ((n : L) : G) ∈ N.map L.subtype := mem_map_of_mem L.subtype n.property
  have hc : ((n : L) : G) * p ∈ centralizer (L : Set G) := by
    intro l hl
    have hh := congrArg L.subtype (hn ⟨l,hl⟩)
    change p*l*p⁻¹ = ((n : L) : G)⁻¹*l*n at hh
    calc
      l * (((n : L) : G)*p) = n * (((n : L) : G)⁻¹*l*n) * p := by group
      _ = n * (p*l*p⁻¹) * p := by rw [←hh]
      _ = (((n : L) : G)*p)*l := by group
  have hm := mul_mem_sup ((N.map L.subtype).inv_mem hnG)
    (show ((n : L) : G)*p ∈ P ⊓ centralizer (L : Set G) from
      ⟨P.mul_mem (hNP hnG) hp,hc⟩)
  simpa only [inv_mul_cancel_left] using hm

end Subgroup
