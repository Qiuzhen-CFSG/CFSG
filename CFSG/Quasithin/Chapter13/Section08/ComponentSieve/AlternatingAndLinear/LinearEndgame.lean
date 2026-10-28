module

public import Theory.Representation.BinaryOffender.FixedGenerator
public import Theory.Representation.BinaryOffender.SmallRank

/-!
# The terminal noncyclic argument in 13.8.25

Write `U` for `Ũ_H`, `W` for its maximal submodule, `I ≤ W` for the chosen
irreducible submodule, `D` for the image of `D_H`, and `A` for `Uγ*`.
The lower bounds on `I/(I ∩ D)` and the quotient fixed codimension,
the critical rank bound, and the symmetry consequence force `m(A)=3`, `dim(U/D)=2`, and `W+D=U`.
The critical commutator line therefore bounds the entire quotient's
commutator by one dimension. The natural quotient, with `A` fixing the
marked plane, contradicts this through the displacement-map injection.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
13.8.25, final two paragraphs, printed p.962 (combined manuscript,
1 March 2004). The natural-module identifications below are actual group
and equivariant linear equivalences. Constructing these identifications,
the chief factors, the plane, and the critical-pair inputs remains with
the source application. These theorems do not assert the whole of 13.8.25.
-/

public section

namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear
open Representation.BinaryOffender
variable {H U : Type*} [Group H] [AddCommGroup U] [Module (ZMod 2) U]
  [FiniteDimensional (ZMod 2) U] (ρ : Representation (ZMod 2) H U)

private theorem codim_mono {D F : Submodule (ZMod 2) U} (h : D ≤ F) :
    Module.finrank (ZMod 2) (U ⧸ F) ≤ Module.finrank (ZMod 2) (U ⧸ D) := by
  have := D.finrank_quotient_add_finrank
  have := F.finrank_quotient_add_finrank
  have := Submodule.finrank_mono h
  omega

/-- The final rank reduction in 13.8.25: the submodule contributes at least two
dimensions; equality in the critical bound would force a second contribution
of at least two. Thus the actor has rank three, the critical codimension is
two, and the maximal submodule supplements the critical subspace. -/
theorem noncyclic_rank_three_reduction
    (W I : Subrepresentation ρ) (hIW : I ≤ W) (D : Submodule (ZMod 2) U)
    (A : Subgroup H) (hsmall : rank A ≤ 3)
    (hbound : Module.finrank (ZMod 2) (U ⧸ D) ≤ rank A)
    (hIcodim : 2 ≤ Module.finrank (ZMod 2)
      (I.toSubmodule ⧸ D.comap I.toSubmodule.subtype))
    (hQcodim : 2 ≤ fixedCodim W.quotientRepresentation A)
    (hsym : Module.finrank (ZMod 2) (U ⧸ D) = rank A → D ≤ fixedSpace ρ A) :
    rank A = 3 ∧ Module.finrank (ZMod 2) (U ⧸ D) = 2 ∧ W.toSubmodule ⊔ D = ⊤ := by
  have hdecI := codim_decomposition I.toSubmodule D
  have hquot := codim_mono (sup_le_sup_right (show I.toSubmodule ≤ W.toSubmodule from hIW) D)
  have hstrict : Module.finrank (ZMod 2) (U ⧸ D) < rank A := by
    by_contra hn
    have heq : Module.finrank (ZMod 2) (U ⧸ D) = rank A := by omega
    have hD := hsym heq
    have hmap : D.map W.toSubmodule.mkQ ≤ fixedSpace W.quotientRepresentation A := by
      rintro _ ⟨d, hd, rfl⟩ a
      change W.toSubmodule.mkQ (ρ a d) = W.toSubmodule.mkQ d
      exact congrArg W.toSubmodule.mkQ (hD hd a)
    have hq := codim_mono hmap
    have hdimeq := (Submodule.quotientQuotientEquivQuotientSup W.toSubmodule D).finrank_eq
    change _ ≤ Module.finrank (ZMod 2)
      ((U ⧸ W.toSubmodule) ⧸ D.map W.toSubmodule.mkQ) at hq
    change fixedCodim W.quotientRepresentation A ≤ _ at hq
    omega
  have hA : rank A = 3 := by omega
  have hD : Module.finrank (ZMod 2) (U ⧸ D) = 2 := by omega
  refine ⟨hA, hD, ?_⟩
  have hzero : Module.finrank (ZMod 2) (U ⧸ (W.toSubmodule ⊔ D)) = 0 := by omega
  apply Submodule.eq_top_of_finrank_eq
  have := (W.toSubmodule ⊔ D).finrank_quotient_add_finrank
  omega

/-- The last noncyclic contradiction in 13.8.25, retaining the geometric rank-
three displacement input explicitly. -/
theorem noncyclic_endgame
    (W I : Subrepresentation ρ) (hIW : I ≤ W) (D S : Submodule (ZMod 2) U)
    (A : Subgroup H) (hsmall : rank A ≤ 3)
    (hbound : Module.finrank (ZMod 2) (U ⧸ D) ≤ rank A)
    (hIcodim : 2 ≤ Module.finrank (ZMod 2)
      (I.toSubmodule ⧸ D.comap I.toSubmodule.subtype))
    (hQcodim : 2 ≤ fixedCodim W.quotientRepresentation A)
    (hsym : Module.finrank (ZMod 2) (U ⧸ D) = rank A → D ≤ fixedSpace ρ A)
    (hS : Module.finrank (ZMod 2) S ≤ 1)
    (hcomm : ∀ a ∈ A, ∀ d ∈ D, ρ a d - d ∈ S)
    (hradical : rank A = 3 →
      1 < Module.finrank (ZMod 2) (subspaceCommutator W.quotientRepresentation ⊤ A)) :
    False := by
  obtain ⟨hA, _, hsup⟩ := noncyclic_rank_three_reduction ρ W I hIW D A hsmall
    hbound hIcodim hQcodim hsym
  have hle := Submodule.finrank_mono
    (quotient_commutator_le_of_supplement ρ W D S A hsup hcomm)
  have hmap := Submodule.finrank_map_le W.toSubmodule.mkQ S
  have hgt := hradical hA
  omega

/-- The same contradiction with the geometric input discharged for an actual
four-dimensional natural quotient. The specified plane is fixed pointwise by
the actor, as holds in the radical of its stabilizer. Both the group and
module identifications are actual equivalences. -/
theorem noncyclic_endgame_of_natural_quotient
    (W I : Subrepresentation ρ) (hIW : I ≤ W) (D S : Submodule (ZMod 2) U)
    (A : Subgroup H) (hsmall : rank A ≤ 3)
    (hbound : Module.finrank (ZMod 2) (U ⧸ D) ≤ rank A)
    (hIcodim : 2 ≤ Module.finrank (ZMod 2)
      (I.toSubmodule ⧸ D.comap I.toSubmodule.subtype))
    (hQcodim : 2 ≤ fixedCodim W.quotientRepresentation A)
    (hsym : Module.finrank (ZMod 2) (U ⧸ D) = rank A → D ≤ fixedSpace ρ A)
    (hS : Module.finrank (ZMod 2) S ≤ 1)
    (hcomm : ∀ a ∈ A, ∀ d ∈ D, ρ a d - d ∈ S)
    (eH : H ≃* ((Fin 4 → ZMod 2) ≃ₗ[ZMod 2] (Fin 4 → ZMod 2)))
    (eQ : (U ⧸ W.toSubmodule) ≃ₗ[ZMod 2] (Fin 4 → ZMod 2))
    (heQ : ∀ g q, eQ (W.quotientRepresentation g q) = eH g (eQ q))
    (P : Submodule (ZMod 2) (Fin 4 → ZMod 2)) (hP : Module.finrank (ZMod 2) P = 2)
    (hPfix : ∀ a ∈ A, ∀ p ∈ P, eH a p = p) : False := by
  have hfaithful : Function.Injective W.quotientRepresentation := by
    intro g h hgh
    apply eH.injective
    ext x
    obtain ⟨q, rfl⟩ := eQ.surjective x
    rw [← heQ g q, ← heQ h q, hgh]
  let F := P.comap eQ.toLinearMap
  have hF : F ≤ fixedSpace W.quotientRepresentation A := by
    intro q hq a
    apply eQ.injective
    exact (heQ a q).trans (hPfix a a.property (eQ q) hq)
  have hFdim : Module.finrank (ZMod 2) ((U ⧸ W.toSubmodule) ⧸ F) ≤ 2 := by
    have he := (Submodule.Quotient.equiv F P eQ
      (Submodule.map_comap_eq_of_surjective eQ.surjective P)).finrank_eq
    have hd := P.finrank_quotient_add_finrank
    have hfour : Module.finrank (ZMod 2) (Fin 4 → ZMod 2) = 4 := by simp
    omega
  apply noncyclic_endgame ρ W I hIW D S A hsmall hbound hIcodim hQcodim
    hsym hS hcomm
  intro hrank
  exact rank_three_commutator_dim_gt_one W.quotientRepresentation hfaithful A F
    hF hFdim hrank

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear
