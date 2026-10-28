module

public import CFSG.Quasithin.ChapterK.Section01To04.Alternating.Recognition.Seven.Degree.Inputs
public import CFSG.Quasithin.ChapterK.Section01To04.Alternating.Recognition.Seven.Degree.Reduction
public import Theory.Representation.AlternatingSevenConjugatePair.ElementaryGeometry.TwoConjugates
public import Theory.Representation.BinaryOffender.SubgroupConjugateDimension

/-!
# Excluding the fourteen-dimensional A₇ module at cubic ratio two

The original ambient cubic bound and the degree reduction supply an elementary
actor A of rank three with fixed codimension at most six. In the faithful
seven-point embedding, A and one even conjugate generate S₇. The literal
component marking lifts that conjugator back to L, and injectivity lifts the
generation statement back to G. Faithful irreducibility on L makes the common
fixed space zero. The two conjugate fixed spaces have equal codimension, so
the degree is at most twelve, contradicting fourteen.

This proves the `NoFourteen` obligation used by the numerical assembly of
Aschbacher–Smith K.1.2, printed p.452/PDF p.463. It retains the original ambient
action and cubic ratio bound; it requires neither a fourteen-dimensional model
nor a classification of binary modules. The fixed-space estimate is the subgroup
form of Guralnick–Malle (2002), §2, inequalities (2.5)–(2.6).
-/

public section
open Subgroup Equiv Representation Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.ChapterK.Alternating

universe u v
variable {G : Type u} {V : Type v} [Group G] [Finite G] [AddCommGroup V]
  [Module (ZMod 2) V] (ρ : Representation (ZMod 2) G V) {K : GroupClass.{u}}
  {L : Subgroup G}

namespace SevenFourteen

/-- The rank-three actor and one conjugate by an element of the actual
component generate the original ambient group. -/
theorem exists_generating_conjugate (h : Input ρ K L)
    (e : L ≃* alternatingGroup (Fin 7)) (A : Subgroup G)
    (hA : IsElementaryTwo A) (hr : rank A = 3) :
    ∃ l : L, A ⊔ A.map (MulAut.conj l.val).toMonoidHom = ⊤ := by
  obtain ⟨f, hf, hmark⟩ := SevenDegreeReduction.exists_permutation_embedding ρ h e
  let B := A.map f
  let : IsElementaryAbelian 2 A := hA.2
  have hB : IsElementaryTwo B :=
    ⟨fun hb => hA.1 ((Subgroup.map_eq_bot_iff_of_injective A hf).mp hb),
      IsElementaryAbelian.map f⟩
  have hrB : rank B = 3 := by
    unfold rank
    rw [Subgroup.card_map_of_injective hf]
    exact hr
  obtain ⟨q, hq, hgen⟩ :=
    AlternatingSevenConjugatePair.ElementaryGeometry.rank_three_two_even_conjugates B hB hrB
  let l := e.symm ⟨q, hq⟩
  have hfl : f l.val = q := (hmark l).trans
    (congrArg Subtype.val (e.apply_symm_apply ⟨q, hq⟩))
  have he : (A.map (MulAut.conj l.val).toMonoidHom).map f =
      B.map (MulAut.conj q).toMonoidHom := by
    change (A.map (MulAut.conj l.val).toMonoidHom).map f =
      (A.map f).map (MulAut.conj q).toMonoidHom
    rw [Subgroup.map_map, Subgroup.map_map]
    congr 1
    ext x
    simp [MulAut.conj_apply, hfl]
  have htop : (A ⊔ A.map (MulAut.conj l.val).toMonoidHom).map f = ⊤ := by
    rw [Subgroup.map_sup, he]
    exact hgen
  refine ⟨l, top_unique ?_⟩
  intro x _
  obtain ⟨a, ha, hax⟩ := (show f x ∈
    (A ⊔ A.map (MulAut.conj l.val).toMonoidHom).map f by rw [htop]; trivial)
  exact hf hax ▸ ha

variable [FiniteDimensional (ZMod 2) V]

/-- Two component conjugates bound the degree by twice the fixed codimension
of the original rank-three actor. -/
theorem finrank_le_twice_fixedCodim (h : Input ρ K L)
    (e : L ≃* alternatingGroup (Fin 7)) (A : Subgroup G)
    (hA : IsElementaryTwo A) (hr : rank A = 3) :
    Module.finrank (ZMod 2) V ≤ 2 * fixedCodim ρ A := by
  obtain ⟨l, hl⟩ := exists_generating_conjugate ρ h e A hA hr
  let : Nontrivial L := e.symm.injective.nontrivial
  let c : Bool → G := fun b => if b then 1 else l.val
  have hc : L ≤ ⨆ b, A.map (MulAut.conj (c b)).toMonoidHom := by
    have hid : (MulAut.conj (1 : G)).toMonoidHom = MonoidHom.id G := by
      ext x
      simp
    simp only [iSup_bool_eq, c, Bool.false_eq_true, ite_false, ite_true, hid,
      Subgroup.map_id, hl]
    exact le_top
  simpa only [Fintype.card_bool] using
    finrank_le_card_mul_fixedCodim_of_subgroup_conjugates ρ L A
      (fixedSpace_eq_bot_of_faithful_irreducible_on ρ L h.faithful h.irreducible) c hc

end SevenFourteen

/-- K.1.2's degree-fourteen exclusion at the original ambient cubic bound two.
No classification or recognition of fourteen-dimensional modules is required. -/
theorem sevenNoFourteen : RecognitionInputs.Seven.Degree.NoFourteen.{u,v} := by
  intro G V _ _ _ _ _ ρ K L h e hd
  obtain ⟨A, hA, _, hr, _, hs⟩ := SevenDegreeReduction.exists_rank_three_cubic_actor
    ρ h e (by omega)
  have hb := SevenFourteen.finrank_le_twice_fixedCodim ρ h e A hA hr
  omega

end CFSG.Quasithin.ChapterK.Alternating
