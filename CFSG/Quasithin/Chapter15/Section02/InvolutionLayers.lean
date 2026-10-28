module

public import CFSG.Quasithin.Chapter15.Section02.CriticalPair
public import Theory.GroupTheory.InvolutionGeneratedElementary

/-!
# The involution-generated layers in the Case-II critical pair

Lemma 15.2.28 bounds `[UH, Λ(QH)]` by `ZS`. Since `UH` and its conjugate
are elementary abelian, this gives both layer bounds used by the terminal
critical-pair contradiction. Conjugation transports the same local bound
to the other endpoint. The local-to-ambient theorem applies the normal-closure
argument inside the original `H`, retaining its literal subtype map.

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*, combined
manuscript (1 March 2004), Lemma 15.2.28 and the final argument on pp.1119--1120.
The source must still provide `ZS` normal in `H` (15.2.11), containment of the
involutions of `T` in `S` and `[V,S] ≤ ZS` (15.2.25), the global parameter
bound, the disjoint centers and the critical pair with its corank-one bounds.
-/

public section

open Subgroup
namespace CFSG.Quasithin.Chapter15.Section02
open ChapterE

variable {G : Type*} [Group G]

/-- The original local normal-closure argument, transported to the ambient group. -/
theorem source_local_normalClosure_involution_bound
    (H : Subgroup G) (V Q T S Z : Subgroup H) [Q.Normal] [Z.Normal]
    (hQT : Q ≤ T) (hTS : ∀ x ∈ T, x ^ 2 = 1 → x ∈ S)
    (hcomm : ⁅V, S⁆ ≤ Z) :
    ⁅(normalClosure (V : Set H)).map H.subtype,
      involutionGenerated (Q.map H.subtype)⁆ ≤ Z.map H.subtype := by
  rw [← map_involutionGenerated_of_injective Q H.subtype Subtype.val_injective,
    ← map_commutator]
  exact Subgroup.map_mono
    (normalClosure_commutator_involutionGenerated_le V Q T S Z hQT hTS hcomm)

/-- Elementary normal-closure layers supply both bounds used on printed p.1120. -/
theorem source_critical_layer_bounds (UH QH ZS : Subgroup G)
    [IsElementaryAbelian 2 UH] (g : G)
    (hbound : ⁅UH, involutionGenerated QH⁆ ≤ ZS) :
    ⁅UH, UH.map (MulAut.conj g).toMonoidHom ⊓ QH⁆ ≤ ZS ∧
    ⁅UH.map (MulAut.conj g).toMonoidHom,
      UH ⊓ QH.map (MulAut.conj g).toMonoidHom⁆ ≤
      ZS.map (MulAut.conj g).toMonoidHom := by
  let f := (MulAut.conj g).toMonoidHom
  let _ : IsElementaryAbelian 2 (UH.map f) := IsElementaryAbelian.map f
  refine ⟨(commutator_mono le_rfl
    (elementary_inf_le_involutionGenerated (UH.map f) QH)).trans hbound, ?_⟩
  have hm := Subgroup.map_mono (f := f) hbound
  rw [map_commutator, map_involutionGenerated_of_injective QH f (MulAut.conj g).injective] at hm
  exact (commutator_mono le_rfl
    (elementary_inf_le_involutionGenerated UH (QH.map f))).trans hm

/-- Apply the terminal contradiction using the single original 15.2.28 bound. -/
theorem source_critical_pair_false_of_involution_bound [Finite G]
    (V QH UH ZS : Subgroup G) [IsElementaryAbelian 2 V]
    [IsElementaryAbelian 2 UH] (g : G)
    (hs : 1 < globalS V) (hVU : V ≤ UH)
    (hfirst : subgroupCorank V (V ⊓ QH.map (MulAut.conj g).toMonoidHom) ≤ 1)
    (hsecond : subgroupCorank (V.map (MulAut.conj g).toMonoidHom)
      (V.map (MulAut.conj g).toMonoidHom ⊓ QH) ≤ 1)
    (hbound : ⁅UH, involutionGenerated QH⁆ ≤ ZS)
    (hcenters : ZS ⊓ ZS.map (MulAut.conj g).toMonoidHom = ⊥)
    (hmove : ⁅V, V.map (MulAut.conj g).toMonoidHom⁆ ≠ ⊥) : False := by
  obtain ⟨hleft, hright⟩ := source_critical_layer_bounds UH QH ZS g hbound
  exact source_critical_pair_false_of_layer_bounds V QH UH ZS g hs hVU
    hfirst hsecond hleft hright hcenters hmove

attribute [local instance] IsElementaryAbelian.map

/-- The literal local-data application: the orbit span and its ambient
commutator bound are constructed inside `H`, not additional premises. -/
theorem source_critical_pair_false_of_local_data [Finite G]
    (H : Subgroup G) (V Q T S Z : Subgroup H) [Q.Normal] [Z.Normal]
    [IsElementaryAbelian 2 V] [IsElementaryAbelian 2 (normalClosure (V : Set H))]
    (g : G) (hQT : Q ≤ T) (hTS : ∀ x ∈ T, x ^ 2 = 1 → x ∈ S)
    (hcomm : ⁅V, S⁆ ≤ Z) (hs : 1 < globalS (V.map H.subtype))
    (hfirst : subgroupCorank (V.map H.subtype)
      (V.map H.subtype ⊓ (Q.map H.subtype).map (MulAut.conj g).toMonoidHom) ≤ 1)
    (hsecond : subgroupCorank ((V.map H.subtype).map (MulAut.conj g).toMonoidHom)
      ((V.map H.subtype).map (MulAut.conj g).toMonoidHom ⊓ Q.map H.subtype) ≤ 1)
    (hcenters : Z.map H.subtype ⊓
      (Z.map H.subtype).map (MulAut.conj g).toMonoidHom = ⊥)
    (hmove : ⁅V.map H.subtype,
      (V.map H.subtype).map (MulAut.conj g).toMonoidHom⁆ ≠ ⊥) : False := by
  let _ : IsElementaryAbelian 2 (V.map H.subtype) := IsElementaryAbelian.map H.subtype
  let _ : IsElementaryAbelian 2 ((normalClosure (V : Set H)).map H.subtype) :=
    IsElementaryAbelian.map H.subtype
  exact source_critical_pair_false_of_involution_bound (V.map H.subtype)
    (Q.map H.subtype) ((normalClosure (V : Set H)).map H.subtype) (Z.map H.subtype)
    g hs (Subgroup.map_mono le_normalClosure) hfirst hsecond
    (source_local_normalClosure_involution_bound H V Q T S Z hQT hTS hcomm)
    hcenters hmove

end CFSG.Quasithin.Chapter15.Section02
