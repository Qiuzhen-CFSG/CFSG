module

public import Theory.AtlasPort.LinearGroups.G2.SolvableSylowPlacement.WeylAction
public import Theory.AtlasPort.LinearGroups.G2.SolvableSylowPlacement.Bruhat
public import Theory.AtlasPort.LinearGroups.G2.LongRootNormalGeneration
public import Theory.AtlasPort.LinearGroups.G2.LieParabolicSetup
public import Theory.AtlasPort.LinearGroups.G2.EvenLocal.ShortCore
public import Theory.AtlasPort.LinearGroups.G2.EvenLocal.LongCore
public import Theory.GroupTheory.PCoreOvergroup
public import Theory.GroupTheory.GeneralizedFitting.SelfCentralizingPrimeCore
public import Theory.Quasithin.EvenCharacteristic

/-!
# Proper Sylow overgroups in the split-octonion G₂ model

Root descent strips a simple reflection even when the Bruhat representative
retains a torus factor: the torus normalizes the positive roots. Two simple
reflections together with the positive roots generate the whole group by
rank-one words. Thus a proper Sylow overgroup lies in one of the two root
parabolics. Their proved self-centralizing two-cores give the same property
in the overgroup.

Source: GLS III, Theorems 2.3.5 and 2.6.5–2.6.7; Aschbacher–Smith B.1.13,
printed p.74. This extends the root descent in G2/EvenLocal/BorelOvergroups.
The octonion coordinates use the licensed ATLAS port (LICENSES/ATLAS.txt).
-/

public section

open Subgroup Atlas.G2 Atlas.G2.Explicit Atlas.G2.LieParabolicSetup
open Atlas.G2.SolvableSylowPlacement

namespace Atlas.G2.ProperSylowOvergroups

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
    (i : Fin 12) (hi : i ≠ 0) (t : Model F) (ht : t ∈ splitTorus)
    (hwi : weylRep i * t ∈ Q) :
    simpleLift (headShort i) ∈ Q := by
  obtain ⟨x,hx,hpar⟩ := exists_negative_simple_conjugate_with_parity (F := F) i hi
  have he : weylRep i * x * (weylRep i)⁻¹ =
      simpleLift (headShort i) * simpleRoot (headShort i) *
        (simpleLift (headShort i))⁻¹ := by
    rcases hpar with ⟨hp,he⟩ | ⟨hp,he⟩
    · simpa [headShort, hp, simpleLift, simpleRoot] using he
    · simpa [headShort, hp, simpleLift, simpleRoot] using he
  have hx' : t⁻¹ * x * t ∈ unipotent := by
    simpa only [inv_inv] using torus_normalizes_unipotent (splitTorus.inv_mem ht) hx
  have hneg := Q.mul_mem (Q.mul_mem hwi (hUQ hx')) (Q.inv_mem hwi)
  have hc : (weylRep i * t) * (t⁻¹ * x * t) * (weylRep i * t)⁻¹ =
      weylRep i * x * (weylRep i)⁻¹ := by group
  rw [hc, he] at hneg
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
    (i : Fin 12) (hi : 3 ≤ i.val) (t : Model F) (ht : t ∈ splitTorus)
    (hwi : weylRep i * t ∈ Q) :
    weylR ∈ Q ∧ weylS ∈ Q := by
  have hi0 : i ≠ 0 := by intro h; subst i; simp at hi
  have hh := head_mem Q hUQ i hi0 t ht hwi
  have htail : weylRep (tailIndex i) * t ∈ Q := by
    rw [← tail_eq i hi0, mul_assoc]
    exact Q.mul_mem (Q.inv_mem hh) hwi
  have ht0 : tailIndex i ≠ 0 := by
    fin_cases i <;> norm_num at hi <;> decide
  have hh' := head_mem Q hUQ (tailIndex i) ht0 t ht htail
  fin_cases i <;> norm_num at hi
  all_goals simp only [tailIndex, headShort, simpleLift] at hh hh'
  all_goals first | exact ⟨hh, hh'⟩ | exact ⟨hh', hh⟩

omit [CharP F 2] in
private theorem eq_top_of_both_simple (H : Subgroup (Model F)) (hU : unipotent ≤ H)
    (hR : weylR ∈ H) (hS : weylS ∈ H) : H = ⊤ := by
  have hE (a:F) : rootE a ∈ H :=
    hU (Subgroup.subset_closure (by simp))
  have hF (a:F) : rootF a ∈ H :=
    hU (Subgroup.subset_closure (by simp))
  have hlong (a:Fˣ) : torus (-1) a * weylR ∈ H := by
    rw [← long_rank_one_word]
    exact H.mul_mem (H.mul_mem (hE _) (H.mul_mem (H.mul_mem hR (hE _)) (H.inv_mem hR))) (hE _)
  have hshort (a:Fˣ) : torus a (-a⁻¹) * weylS ∈ H := by
    rw [← short_rank_one_word]
    exact H.mul_mem (H.mul_mem (hF _) (H.mul_mem (H.mul_mem hS (hF _)) (H.inv_mem hS))) (hF _)
  have htm (a:Fˣ) : torus 1 a ∈ H := by
    have h := H.mul_mem (hlong a) (H.inv_mem (hlong 1))
    rw [mul_inv_rev,← mul_assoc,mul_assoc (torus (-1) a),mul_inv_cancel,mul_one,
      torus_inverse,torus_product] at h
    simpa using h
  have htd (a:Fˣ) : torus a a⁻¹ ∈ H := by
    have h := H.mul_mem (hshort a) (H.inv_mem (hshort 1))
    rw [mul_inv_rev,← mul_assoc,mul_assoc (torus a (-a⁻¹)),mul_inv_cancel,mul_one,
      torus_inverse,torus_product] at h
    simpa using h
  have ht (a b:Fˣ) : torus a b ∈ H := by
    have h := H.mul_mem (htd a) (htm (a*b))
    rw [torus_product] at h
    simpa using h
  have hr : (weylR : Model F) ∈ H := by
    have h := H.mul_mem (H.inv_mem (ht (-1) 1)) (hlong 1)
    simpa only [inv_mul_cancel_left] using h
  have hs : (weylS : Model F) ∈ H := by
    have h := H.mul_mem (H.inv_mem (ht 1 (-1))) (hshort 1)
    simpa only [inv_one,inv_mul_cancel_left] using h
  apply top_unique
  rw [← generated_eq_top]
  apply sup_le
  · apply (Subgroup.closure_le H).mpr
    intro g hg
    rcases hg with hg | hg
    · exact hU hg
    · simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hg
      rcases hg with rfl | rfl
      · exact hr
      · exact hs
  · rintro g ⟨⟨a,b⟩,rfl⟩
    exact ht a b

private theorem weyl_index_lt_three (Q : Subgroup (Model F)) (hUQ : unipotent ≤ Q)
    (hQ : Q < ⊤) (i : Fin 12) (t : Model F) (ht : t ∈ splitTorus)
    (hi : weylRep i * t ∈ Q) : i.val < 3 := by
  by_contra! hn
  obtain ⟨hR,hS⟩ := both_simple_mem Q hUQ i hn t ht hi
  exact hQ.ne (eq_top_of_both_simple Q hUQ hR hS)

/-- Root descent turns the twelve-cell factorization into standard parabolic
coverage of every proper positive-root overgroup. -/
theorem le_parabolic_of_bruhatCover (hBruhat : BruhatCover F)
    (Q : Subgroup (Model F)) (hUQ : unipotent ≤ Q) (hQ : Q < ⊤) :
    Q ≤ parabolic₁ ∨ Q ≤ parabolic₂ := by
  have hfactor (g : Model F) (hg : g ∈ Q) :
      ∃ (i : Fin 12) (u : Model F), u ∈ unipotent ∧
        ∃ t ∈ splitTorus, ∃ v ∈ unipotent,
          g = u * weylRep i * t * v ∧ i.val < 3 ∧ weylRep i * t ∈ Q := by
    obtain ⟨i,u,hu,t,ht,v,hv,he⟩ := hBruhat g
    have hwi : weylRep i * t ∈ Q := by
      have h := Q.mul_mem
        (Q.mul_mem (Q.inv_mem (hUQ hu)) hg) (Q.inv_mem (hUQ hv))
      simpa [he, mul_assoc] using h
    exact ⟨i,u,hu,t,ht,v,hv,he,weyl_index_lt_three Q hUQ hQ i t ht hwi,hwi⟩
  by_cases hR : (weylR : Model F) ∈ Q
  · have hS : (weylS : Model F) ∉ Q :=
      fun hS => hQ.ne (eq_top_of_both_simple Q hUQ hR hS)
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
    · apply False.elim
      apply hS
      have hh := head_mem Q hUQ 2 (by decide) t ht hwi
      simpa [simpleLift, headShort] using hh
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
    · apply False.elim
      apply hR
      have hh := head_mem Q hUQ 1 (by decide) t ht hwi
      simpa [simpleLift, headShort] using hh
    · exact mem_sup_right (subset_closure (by simp [weylRep]))

/-- Every proper positive-root overgroup is contained in one of the two standard
root parabolics of the actual split-octonion group. -/
theorem le_parabolic (Q : Subgroup (Model F)) (hUQ : unipotent ≤ Q) (hQ : Q < ⊤) :
    Q ≤ parabolic₁ ∨ Q ≤ parabolic₂ :=
  le_parabolic_of_bruhatCover bruhatCover Q hUQ hQ

/-- Exhaustive placement with the original Sylow marking, without a
nontrivial-core or solvability premise. -/
theorem conjugate_le_parabolic [Finite F]
    (S : Sylow 2 (Model F)) (X : Subgroup (Model F))
    (hSX : (S : Subgroup (Model F)) ≤ X) (hX : X ≠ ⊤) :
    ∃ g : Model F,
      X.map (MulAut.conj g).toMonoidHom ≤ parabolic₁ ∨
        X.map (MulAut.conj g).toMonoidHom ≤ parabolic₂ := by
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (Model F) S (sylow (F := F))
  have hSU : (S : Subgroup (Model F)).map (MulAut.conj g).toMonoidHom =
      unipotent := by
    rw [← sylow_coe, ← hg, Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
    rfl
  refine ⟨g, le_parabolic _ (hSU ▸ Subgroup.map_mono hSX) ?_⟩
  apply lt_top_iff_ne_top.mpr
  intro ht
  apply hX
  apply Subgroup.map_injective (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).injective
  rw [Subgroup.map_top_of_surjective _ (MulAut.conj g).surjective]
  exact ht

private theorem restriction {A : Type*} [Group A] [Finite A]
    (Q : Sylow 2 A) (H P : Subgroup A)
    (hQH : (Q : Subgroup A) ≤ H) (hHP : H ≤ P)
    (hP : centralizer (pCore 2 P : Set P) ≤ pCore 2 P) :
    centralizer (pCore 2 H : Set H) ≤ pCore 2 H := by
  have h := centralizer_pCore_le_of_sylow_le (Q.subtype (hQH.trans hHP))
    (H.subgroupOf P) (fun _ hx => hQH hx) hP
  exact (Theory.Quasithin.centralizer_pCore_le_iff 2
    (subgroupOfEquivOfLe hHP)).mp h

/-- Every proper Sylow overgroup in the actual G₂ carrier has characteristic
two, by restriction from the two explicit root parabolics. -/
theorem centralizer_twoCore_le [Finite F]
    (S : Sylow 2 (Model F)) (X : Subgroup (Model F))
    (hSX : (S : Subgroup (Model F)) ≤ X) (hX : X ≠ ⊤) :
    centralizer (pCore 2 X : Set X) ≤ pCore 2 X := by
  obtain ⟨g, hg⟩ := conjugate_le_parabolic S X hSX hX
  let e := MulAut.conj g
  let T := S.mapSurjective (f := e.toMonoidHom) e.surjective
  have hTX : (T : Subgroup (Model F)) ≤ X.map e.toMonoidHom := map_mono hSX
  have hc : centralizer (pCore 2 (X.map e.toMonoidHom) : Set (X.map e.toMonoidHom)) ≤
      pCore 2 (X.map e.toMonoidHom) := by
    rcases hg with hg | hg
    · exact restriction T _ parabolic₁ hTX hg EvenLocal.parabolic₁_centralizer_pCore
    · exact restriction T _ parabolic₂ hTX hg EvenLocal.parabolic₂_centralizer_pCore
  exact (Theory.Quasithin.centralizer_pCore_le_iff 2 (e.subgroupMap X)).mpr hc

/-- The generalized Fitting subgroup of each proper Sylow overgroup is
exactly its two-core. This includes the full G₂(2) carrier. -/
theorem generalizedFitting_eq_twoCore [Finite F]
    (S : Sylow 2 (Model F)) (X : Subgroup (Model F))
    (hSX : (S : Subgroup (Model F)) ≤ X) (hX : X ≠ ⊤) :
    Theory.GroupTheory.generalizedFitting X = pCore 2 X :=
  Theory.GroupTheory.generalizedFitting_eq_pCore_of_selfCentralizing 2
    (centralizer_twoCore_le S X hSX hX)

end Atlas.G2.ProperSylowOvergroups
