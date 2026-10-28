module

public import Theory.AtlasPort.LinearGroups.G2.SolvableSylowPlacement.WeylAction
public import Theory.AtlasPort.LinearGroups.G2.SolvableSylowPlacement.Bruhat
public import Theory.AtlasPort.LinearGroups.G2.LongRootNormalGeneration
public import Theory.AtlasPort.LinearGroups.G2.LieParabolicSetup

/-!
# Proper Borel overgroups in even-field G₂

Every proper subgroup containing the standard Borel lies in one of the two
standard root parabolics. Strip the Borel factors from the concrete Bruhat
factorization. Root descent and the rank-one word identity extract the first
simple reflection from a Weyl representative in the subgroup. Removing that
reflection and repeating extracts the other reflection whenever the word has
length at least two. Both reflections together with the Borel generate the
whole group, so only the identity and one simple reflection can occur in a
proper overgroup. Their cells lie in the corresponding standard parabolic.

The proof uses the literal split-octonion automorphism group and holds over
any field of characteristic two, including F₂. In particular it supplies the
finite-field conjugate containment with conjugating element one. It requires
no nonidentity core, maximality hypothesis, or assumed parabolic identification.

Source: GLS III, Theorem 2.6.5(b), with the Bruhat factorization of Theorem
2.3.5, `refs/KGroup/GLS3/chapter2.tex`. The root coordinates are from the licensed
ATLAS port; see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/

public section

open Subgroup Atlas.G2 Atlas.G2.Explicit Atlas.G2.LieParabolicSetup
open Atlas.G2.SolvableSylowPlacement

namespace Atlas.G2.EvenLocal.BorelOvergroups

variable {F : Type*} [Field F] [CharP F 2]

private def simpleLift (short : Bool) : Model F := if short then weylS else weylR

private def simpleRoot (short : Bool) : Model F := if short then rootF 1 else rootE 1

private def headShort (i : Fin 12) : Bool := decide (i.val % 2 = 0)

private def tailIndex (i : Fin 12) : Fin 12 := ![0,0,0,2,1,4,3,6,5,8,7,10] i

private theorem simple_rank_one_word (short : Bool) :
    simpleRoot (F := F) short *
      (simpleLift short * simpleRoot short * (simpleLift short)⁻¹) *
        simpleRoot short = simpleLift short := by
  have hneg : (-1 : Fˣ) = 1 := by
    apply Units.ext
    simp [CharTwo.neg_eq]
  cases short
  · simpa [simpleRoot, simpleLift, hneg, CharTwo.neg_eq, torus_identity] using
      long_rank_one_word (1 : Fˣ)
  · simpa [simpleRoot, simpleLift, hneg, CharTwo.neg_eq, torus_identity] using
      short_rank_one_word (1 : Fˣ)

omit [CharP F 2] in
private theorem simpleRoot_mem (short : Bool) : simpleRoot (F := F) short ∈ unipotent := by
  cases short <;> apply Subgroup.subset_closure <;> simp [simpleRoot]

private theorem head_mem (Q : Subgroup (Model F)) (hUQ : unipotent ≤ Q)
    (i : Fin 12) (hi : i ≠ 0) (hwi : weylRep i ∈ Q) :
    simpleLift (headShort i) ∈ Q := by
  obtain ⟨x,hx,hpar⟩ := exists_negative_simple_conjugate_with_parity (F := F) i hi
  have he : weylRep i * x * (weylRep i)⁻¹ =
      simpleLift (headShort i) * simpleRoot (headShort i) *
        (simpleLift (headShort i))⁻¹ := by
    rcases hpar with ⟨hp,he⟩ | ⟨hp,he⟩
    · simpa [headShort, hp, simpleLift, simpleRoot] using he
    · simpa [headShort, hp, simpleLift, simpleRoot] using he
  have hneg := Q.mul_mem (Q.mul_mem hwi (hUQ hx)) (Q.inv_mem hwi)
  rw [he] at hneg
  have hroot := hUQ (simpleRoot_mem (headShort i))
  have hword := Q.mul_mem (Q.mul_mem hroot hneg) hroot
  rwa [simple_rank_one_word] at hword

omit [CharP F 2] in
private theorem tail_eq (i : Fin 12) (hi : i ≠ 0) :
    (simpleLift (headShort i) : Model F)⁻¹ * weylRep i = weylRep (tailIndex i) := by
  fin_cases i
  · exact (hi rfl).elim
  all_goals simp [simpleLift, headShort, tailIndex, weylRep, mul_assoc]

private theorem both_simple_mem (Q : Subgroup (Model F)) (hUQ : unipotent ≤ Q)
    (i : Fin 12) (hi : 3 ≤ i.val) (hwi : weylRep i ∈ Q) :
    weylR ∈ Q ∧ weylS ∈ Q := by
  have hi0 : i ≠ 0 := by intro h; subst i; simp at hi
  have hh := head_mem Q hUQ i hi0 hwi
  have ht : weylRep (tailIndex i) ∈ Q := by
    rw [← tail_eq i hi0]
    exact Q.mul_mem (Q.inv_mem hh) hwi
  have ht0 : tailIndex i ≠ 0 := by
    fin_cases i <;> norm_num at hi <;> decide
  have hh' := head_mem Q hUQ (tailIndex i) ht0 ht
  fin_cases i <;> norm_num at hi
  all_goals simp only [tailIndex, headShort, simpleLift] at hh hh'
  all_goals first | exact ⟨hh, hh'⟩ | exact ⟨hh', hh⟩

omit [CharP F 2] in
private theorem eq_top_of_both_simple (Q : Subgroup (Model F)) (hBQ : borel ≤ Q)
    (hR : weylR ∈ Q) (hS : weylS ∈ Q) : Q = ⊤ := by
  apply top_unique
  rw [← parabolics_generate (F := F)]
  apply sup_le
  · exact sup_le hBQ ((closure_le _).mpr (by simpa using hS))
  · exact sup_le hBQ ((closure_le _).mpr (by simpa using hR))

private theorem weyl_index_lt_three (Q : Subgroup (Model F)) (hBQ : borel ≤ Q)
    (hQ : Q < ⊤) (i : Fin 12) (hi : weylRep i ∈ Q) : i.val < 3 := by
  by_contra! hn
  obtain ⟨hR,hS⟩ := both_simple_mem Q (le_sup_left.trans hBQ) i hn hi
  exact hQ.ne (eq_top_of_both_simple Q hBQ hR hS)

/-- Root descent turns the twelve-cell factorization into standard parabolic
coverage of every proper Borel overgroup. -/
theorem le_parabolic_of_bruhatCover (hBruhat : BruhatCover F)
    (Q : Subgroup (Model F)) (hBQ : borel ≤ Q) (hQ : Q < ⊤) :
    Q ≤ parabolic₁ ∨ Q ≤ parabolic₂ := by
  have hfactor (g : Model F) (hg : g ∈ Q) :
      ∃ (i : Fin 12) (u : Model F), u ∈ unipotent ∧
        ∃ t ∈ splitTorus, ∃ v ∈ unipotent,
          g = u * weylRep i * t * v ∧ i.val < 3 ∧ weylRep i ∈ Q := by
    obtain ⟨i,u,hu,t,ht,v,hv,he⟩ := hBruhat g
    have hwi : weylRep i ∈ Q := by
      have h := Q.mul_mem
        (Q.mul_mem (Q.mul_mem (Q.inv_mem (hBQ (mem_sup_left hu))) hg)
          (Q.inv_mem (hBQ (mem_sup_left hv))))
        (Q.inv_mem (hBQ (mem_sup_right ht)))
      simpa [he, mul_assoc] using h
    exact ⟨i,u,hu,t,ht,v,hv,he,weyl_index_lt_three Q hBQ hQ i hwi,hwi⟩
  by_cases hR : (weylR : Model F) ∈ Q
  · have hS : (weylS : Model F) ∉ Q :=
      fun hS => hQ.ne (eq_top_of_both_simple Q hBQ hR hS)
    right
    intro g hg
    obtain ⟨i,u,hu,t,ht,v,hv,rfl,hi,hwi⟩ := hfactor g hg
    apply parabolic₂.mul_mem
      (parabolic₂.mul_mem (parabolic₂.mul_mem
        (borel_le_parabolic₂ (mem_sup_left hu)) ?_)
        (borel_le_parabolic₂ (mem_sup_right ht)))
      (borel_le_parabolic₂ (mem_sup_left hv))
    fin_cases i <;> norm_num at hi
    · exact parabolic₂.one_mem
    · exact weylR_mem_parabolic
    · exact (hS hwi).elim
  · left
    intro g hg
    obtain ⟨i,u,hu,t,ht,v,hv,rfl,hi,hwi⟩ := hfactor g hg
    apply parabolic₁.mul_mem
      (parabolic₁.mul_mem (parabolic₁.mul_mem
        (borel_le_parabolic₁ (mem_sup_left hu)) ?_)
        (borel_le_parabolic₁ (mem_sup_right ht)))
      (borel_le_parabolic₁ (mem_sup_left hv))
    fin_cases i <;> norm_num at hi
    · exact parabolic₁.one_mem
    · exact (hR hwi).elim
    · exact mem_sup_right (subset_closure (by simp [weylRep]))

/-- Every proper Borel overgroup is contained in one of the two standard
root parabolics of the actual split-octonion group. -/
theorem le_parabolic (Q : Subgroup (Model F)) (hBQ : borel ≤ Q) (hQ : Q < ⊤) :
    Q ≤ parabolic₁ ∨ Q ≤ parabolic₂ :=
  le_parabolic_of_bruhatCover bruhatCover Q hBQ hQ

/-- The subgroup-map form of proper Borel-overgroup coverage. The standard
Borel hypothesis allows the identity as the conjugating element. -/
theorem conjugate_le_parabolic
    (Q : Subgroup (Model F)) (hBQ : borel ≤ Q) (hQ : Q < ⊤) :
    ∃ g : Model F,
      Q.map (MulAut.conj g).toMonoidHom ≤ parabolic₁ ∨
        Q.map (MulAut.conj g).toMonoidHom ≤ parabolic₂ := by
  refine ⟨1, ?_⟩
  have he : (MulAut.conj (1 : Model F)).toMonoidHom = MonoidHom.id _ := by
    ext x
    simp
  simpa only [he, Subgroup.map_id] using le_parabolic Q hBQ hQ

end Atlas.G2.EvenLocal.BorelOvergroups
