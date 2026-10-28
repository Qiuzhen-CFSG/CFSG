module

public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.LieSieve.LinearThree.Displacement
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.LieSieve.LinearThree.Reduction
public import Theory.SpecificGroups.PSL3.LinearThreeSylow.RootScalars
public import Theory.SpecificGroups.PSL3.LinearThreeSylow.PointwiseFixer
public import Theory.GroupAction.PerfectCentralQuotient
public import CFSG.Quasithin.ChapterE.Section03.Parameters.AutomizerFF
public import Theory.AtlasPort.ExceptionalIsomorphisms.Elementary


/-!
# The actual marked actions in the PSL₃ branches of E.6.8

Conjugation by V on the component L has kernel C_V(L), and fixes the
specified Sylow subgroup pointwise. Its image is nontrivial and is preserved
by conjugation from the marked Borel. Perfectness makes the action on L/Z(L)
faithful to the action on L, with exactly the same kernel. When Z(L) is a
two-group, the entire quotient Borel lifts to the marked Borel upstairs.
These statements include a trivial covering center.

For PSL₃(2), the displacement bound and coprime splitting already prove that
L ∩ M centralizes V, giving the cyclic group of order one in the source.
The intrinsic pointwise-fixer and root-scalar theorems identify the nontrivial
Borel-invariant action image with the entire Sylow center. Its known order
gives the exact corank, also in the faithful central quotient. Transporting
the actual scalar character gives coordinates on V/C_V(L). Coprime splitting
shows that the character kernel is already the kernel of the action on V:
a displacement in C_V(L) lies in both factors of the direct decomposition.
The full induced automizer is consequently cyclic of order 2^n - 1. For
n > 1 the nontrivial scalars also identify C_V(L ∩ M) with C_V(L).

`ordinary_calculations` proves all three action conclusions including n = 1.
`central_quotient_calculations` proves them for central two-covers, and
`four_cover_calculations` specializes to the source PSL₃(4) branch, including
trivial covering center. These results retain the independently supplied
marked Borel placement; `LinearThree.Reduction` assembles the other source
clauses from them. No E.6.11 complement theorem or BorelAlternative is used.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), E.6.8,
printed pp.247–248 (PDF pp.258–259), especially (!) and (*) on p.247.
-/

public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.Section06.Components.LieSieve.LinearThree.MarkedAction
variable {G : Type*} [Group G] [Finite G]
variable {K : GroupClass} {T : Sylow 2 G} {M V U L : Subgroup G}

/-- The literal conjugation action of V on the relatively normalized component. -/
@[expose] def componentAction (h : HypothesisE61 K T M V) (hU : U ∈ obstructionFamily M V)
    (hL : ComponentIn (centralizer (U : Set G)) L) : V →* MulAut L :=
  L.normalizerMonoidHom.comp (inclusion (component_normalized_by_V h hU hL))

/-- Its kernel is the relative centralizer inside V. -/
theorem componentAction_ker (h : HypothesisE61 K T M V) (hU : U ∈ obstructionFamily M V)
    (hL : ComponentIn (centralizer (U : Set G)) L) :
    (componentAction h hU hL).ker = (centralizer (L : Set G)).subgroupOf V := by
  rw [componentAction, ← MonoidHom.comap_ker, normalizerMonoidHom_ker]
  rfl

/-- The source action corank is the binary logarithm of the actual image order. -/
theorem actionCorank_eq_log_range (h : HypothesisE61 K T M V)
    (hU : U ∈ obstructionFamily M V)
    (hL : ComponentIn (centralizer (U : Set G)) L) :
    actionCorank V L = Nat.log 2 (Nat.card (componentAction h hU hL).range) := by
  rw [← index_ker, componentAction_ker]
  exact congrArg (Nat.log 2) (inf_relIndex_left V (centralizer (L : Set G)))

/-- The supplied ambient marking gives pointwise fixation, not just Sylow stability. -/
theorem componentAction_fixes_marked_sylow
    (h : HypothesisE61 K T M V) (hU : U ∈ obstructionFamily M V)
    (hL : ComponentIn (centralizer (U : Set G)) L) (S : Sylow 2 L)
    (hS : (S : Subgroup L).map L.subtype = L ⊓ sylowCentralizer (T : Subgroup G) V)
    (v : V) (s : L) (hs : s ∈ S) : componentAction h hU hL v s = s := by
  apply Subtype.ext
  change (v : G) * (s : G) * (v : G)⁻¹ = s
  have hm := hS ▸ mem_map_of_mem L.subtype hs
  have hc : (v : G) * (s : G) = (s : G) * (v : G) :=
    (mem_centralizer_iff.mp hm.2.2) v v.property
  rw [hc, mul_inv_cancel_right]

/-- Escape of the component from M forces a nontrivial actual image. -/
theorem componentAction_range_ne_bot
    (h : HypothesisE61 K T M V) (earlier : EarlierLocalFacts T)
    (hU : U ∈ obstructionFamily M V)
    (hL : ComponentIn (centralizer (U : Set G)) L) :
    (componentAction h hU hL).range ≠ ⊥ := by
  intro he
  have hp := fixedSpace_corank_pos h (component_not_le h earlier hU hL)
  change 0 < actionCorank V L at hp
  rw [actionCorank_eq_log_range h hU hL, he] at hp
  simp at hp

/-- The action induced by the same conjugation on the actual central quotient. -/
@[expose] def quotientAction (h : HypothesisE61 K T M V) (hU : U ∈ obstructionFamily M V)
    (hL : ComponentIn (centralizer (U : Set G)) L) : V →* MulAut (L ⧸ center L) :=
  (quotientAut (center L)).comp (componentAction h hU hL)

/-- Perfectness preserves the action-image order on passage to the quotient. -/
theorem quotientAction_range_card (h : HypothesisE61 K T M V)
    (hU : U ∈ obstructionFamily M V)
    (hL : ComponentIn (centralizer (U : Set G)) L) :
    Nat.card (quotientAction h hU hL).range =
      Nat.card (componentAction h hU hL).range := by
  let _ := BorelActions.component_quasisimple hL
  rw [quotientAction, MonoidHom.range_comp,
    card_map_of_injective MulAut.quotient_center_injective]

/-- The image of the marked Sylow subgroup is fixed pointwise downstairs. -/
theorem quotientAction_fixes_marked_sylow
    (h : HypothesisE61 K T M V) (hU : U ∈ obstructionFamily M V)
    (hL : ComponentIn (centralizer (U : Set G)) L) (S : Sylow 2 L)
    (hS : (S : Subgroup L).map L.subtype = L ⊓ sylowCentralizer (T : Subgroup G) V)
    (v : V) (s : L ⧸ center L)
    (hs : s ∈ (S : Subgroup L).map (QuotientGroup.mk' (center L))) :
    quotientAction h hU hL v s = s := by
  obtain ⟨x,hx,rfl⟩ := hs
  change quotientAut (center L) (componentAction h hU hL v)
    (QuotientGroup.mk' (center L) x) = _
  rw [quotientAut_apply_mk, componentAction_fixes_marked_sylow h hU hL S hS v x hx]

/-- The central quotient loses no nontrivial component action. -/
theorem quotientAction_range_ne_bot
    (h : HypothesisE61 K T M V) (earlier : EarlierLocalFacts T)
    (hU : U ∈ obstructionFamily M V)
    (hL : ComponentIn (centralizer (U : Set G)) L) :
    (quotientAction h hU hL).range ≠ ⊥ := by
  let _ := BorelActions.component_quasisimple hL
  rw [quotientAction, MonoidHom.range_comp]
  intro he
  exact componentAction_range_ne_bot h earlier hU hL
    ((map_eq_bot_iff_of_injective _
      (MulAut.quotient_center_injective (G := L))).mp he)

/-- Conditional ordinary bound, with the intrinsic pointwise-fixer calculation explicit. -/
theorem actionCorank_le_of_sylow_fixer
    (h : HypothesisE61 K T M V) (hU : U ∈ obstructionFamily M V)
    (hL : ComponentIn (centralizer (U : Set G)) L)
    {n : ℕ} (hn : 1 ≤ n) (iso : ClassicalGroup.IsPSL L 3 (2 ^ n))
    (S : Sylow 2 L)
    (hS : (S : Subgroup L).map L.subtype = L ⊓ sylowCentralizer (T : Subgroup G) V)
    (hfixer : ∀ a : MulAut L, (∀ s ∈ S, a s = s) →
      ∃ z ∈ (center S).map (S : Subgroup L).subtype, a = MulAut.conj z) :
    actionCorank V L ≤ n := by
  have hi : (componentAction h hU hL).range ≤
      ((center S).map (S : Subgroup L).subtype).map MulAut.conj := by
    rintro a ⟨v,rfl⟩
    obtain ⟨z,hz,he⟩ := hfixer (componentAction h hU hL v)
      (componentAction_fixes_marked_sylow h hU hL S hS v)
    exact ⟨z,hz,he.symm⟩
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := iso
  have hc := Matrix.PSL3.LinearThree.card_center_sylow_of_equiv F (by omega) hF e S
  have hb : Nat.card (componentAction h hU hL).range ≤ 2 ^ n := by
    calc
      _ ≤ Nat.card (((center S).map (S : Subgroup L).subtype).map MulAut.conj) := card_le_of_le hi
      _ ≤ Nat.card ((center S).map (S : Subgroup L).subtype) :=
        Nat.le_of_dvd Nat.card_pos (card_map_dvd _ _)
      _ = _ := by rw [card_map_of_injective (S : Subgroup L).subtype_injective, hc]
  rw [actionCorank_eq_log_range h hU hL]
  exact (Nat.log_mono_right hb).trans_eq (Nat.log_pow (by decide : 1 < 2) n)

/-- Conditional quotient bound; the covering center may be trivial. -/
theorem actionCorank_le_of_quotient_sylow_fixer
    (h : HypothesisE61 K T M V) (hU : U ∈ obstructionFamily M V)
    (hL : ComponentIn (centralizer (U : Set G)) L)
    {n : ℕ} (hn : 1 ≤ n) (iso : ClassicalGroup.IsPSL (L ⧸ center L) 3 (2 ^ n))
    (S : Sylow 2 L)
    (hS : (S : Subgroup L).map L.subtype = L ⊓ sylowCentralizer (T : Subgroup G) V)
    (hfixer : ∀ (R : Sylow 2 (L ⧸ center L)) (a : MulAut (L ⧸ center L)),
      (∀ s ∈ R, a s = s) →
      ∃ z ∈ (center R).map (R : Subgroup (L ⧸ center L)).subtype, a = MulAut.conj z) :
    actionCorank V L ≤ n := by
  let q := QuotientGroup.mk' (center L)
  let R := S.mapSurjective (f := q) (QuotientGroup.mk'_surjective _)
  have hi : (quotientAction h hU hL).range ≤
      ((center R).map (R : Subgroup (L ⧸ center L)).subtype).map MulAut.conj := by
    rintro a ⟨v,rfl⟩
    obtain ⟨z,hz,he⟩ := hfixer R (quotientAction h hU hL v)
      (quotientAction_fixes_marked_sylow h hU hL S hS v)
    exact ⟨z,hz,he.symm⟩
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := iso
  have hc := Matrix.PSL3.LinearThree.card_center_sylow_of_equiv F (by omega) hF e R
  have hb : Nat.card (quotientAction h hU hL).range ≤ 2 ^ n := by
    calc
      _ ≤ Nat.card (((center R).map (R : Subgroup (L ⧸ center L)).subtype).map MulAut.conj) :=
        card_le_of_le hi
      _ ≤ Nat.card ((center R).map (R : Subgroup (L ⧸ center L)).subtype) :=
        Nat.le_of_dvd Nat.card_pos (card_map_dvd _ _)
      _ = _ := by rw [card_map_of_injective (R : Subgroup (L ⧸ center L)).subtype_injective, hc]
  rw [quotientAction_range_card] at hb
  rw [actionCorank_eq_log_range h hU hL]
  exact (Nat.log_mono_right hb).trans_eq (Nat.log_pow (by decide : 1 < 2) n)


/-- The two actual conjugation actions satisfy the required equivariance identity. -/
theorem componentAction_conjugate
    (h : HypothesisE61 K T M V) (hU : U ∈ obstructionFamily M V)
    (hL : ComponentIn (centralizer (U : Set G)) L)
    (b : ↥(L ⊓ M)) (v : V) :
    componentAction h hU hL
      (V.normalizerMonoidHom ⟨b, component_intersection_normalizes h hU hL.1 b.property⟩ v) =
      MulAut.conj (⟨b, b.property.1⟩ : L) * componentAction h hU hL v *
        (MulAut.conj (⟨b, b.property.1⟩ : L))⁻¹ := by
  ext x
  change ((b : G) * (v : G) * (b : G)⁻¹) * (x : G) *
      ((b : G) * (v : G) * (b : G)⁻¹)⁻¹ =
    (b : G) * ((v : G) * ((b : G)⁻¹ * (x : G) * (b : G)) * (v : G)⁻¹) * (b : G)⁻¹
  group

/-- Borel placement makes the actual image invariant under every marked Borel element. -/
theorem componentAction_range_stable
    (h : HypothesisE61 K T M V) (hU : U ∈ obstructionFamily M V)
    (hL : ComponentIn (centralizer (U : Set G)) L)
    (S : Sylow 2 L) (hplace : L ⊓ M = markedBorel L S)
    (b : L) (hb : b ∈ normalizer (S : Set L))
    (a : MulAut L) (ha : a ∈ (componentAction h hU hL).range) :
    MulAut.conj b * a * (MulAut.conj b)⁻¹ ∈ (componentAction h hU hL).range := by
  have hbM : (b : G) ∈ L ⊓ M := hplace.symm ▸ mem_map_of_mem L.subtype hb
  obtain ⟨v,rfl⟩ := ha
  exact ⟨V.normalizerMonoidHom
    ⟨b, component_intersection_normalizes h hU hL.1 hbM⟩ v,
    componentAction_conjugate h hU hL ⟨b,hbM⟩ v⟩

private theorem normalizer_le_centralizer_of_card_le_two
    (A : Subgroup G) (hA : Nat.card A ≤ 2) :
    normalizer (A : Set G) ≤ centralizer (A : Set G) := by
  have hp := Nat.card_pos (α := A)
  by_cases h1 : Nat.card A = 1
  · let _ := (Nat.card_eq_one_iff_unique.mp h1).1
    intro g _ a ha
    have he : a = 1 := congrArg Subtype.val (Subsingleton.elim (⟨a,ha⟩ : A) 1)
    simp [he]
  have h2 : Nat.card A = 2 := by omega
  obtain ⟨z, _, hzuniq⟩ := (Nat.card_eq_two_iff' (1 : A)).mp h2
  intro g hg
  apply mem_centralizer_iff.mpr
  intro x hx
  by_cases hxone : x = 1
  · simp [hxone]
  let xA : A := ⟨x, hx⟩
  let yA : A := ⟨g * x * g⁻¹, (hg x).mp hx⟩
  have hyne : yA ≠ 1 := by
    intro hy
    have hy' : g * x * g⁻¹ = 1 := congrArg Subtype.val hy
    apply hxone
    have hh := congrArg (fun a : G => g⁻¹ * a * g) hy'
    simpa [mul_assoc] using hh
  have heq : yA = xA := (hzuniq yA hyne).trans (hzuniq xA (by
    intro hx'
    exact hxone (congrArg Subtype.val hx'))).symm
  have heq' : g * x * g⁻¹ = x := congrArg Subtype.val heq
  have hh := congrArg (fun a : G => a * g) heq'
  simpa [mul_assoc] using hh.symm

/-- For PSL₃(2), the displacement has order at most two and is fixed by its normalizer.
Coprime splitting therefore makes all of V fixed by L ∩ M. -/
theorem binary_intersection_centralizes
    (h : HypothesisE61 K T M V) (hU : U ∈ obstructionFamily M V)
    (hL : ComponentIn (centralizer (U : Set G)) L)
    (iso : ClassicalGroup.IsPSL L 3 2) : L ⊓ M ≤ centralizer (V : Set G) := by
  have hb : Nat.card (⁅V, L ⊓ M⁆ : Subgroup G) ≤ 2 :=
    displacement_card_le_linear_three h hU hL (n := 1) (by decide) iso
  have hW : L ⊓ M ≤ centralizer ((⁅V, L ⊓ M⁆ : Subgroup G) : Set G) :=
    (normalizer_commutator_ge_right V (L ⊓ M)).trans
      (normalizer_le_centralizer_of_card_le_two _ hb)
  have hd := intersection_decomposition h hU hL
  apply le_centralizer_iff.mpr
  rw [← hd.1]
  exact sup_le (le_centralizer_iff.mp hW) inf_le_right

/-- The cyclic action clause for n = 1; no intrinsic fixer input is required. -/
theorem binary_intersection_action
    (h : HypothesisE61 K T M V) (hU : U ∈ obstructionFamily M V)
    (hL : ComponentIn (centralizer (U : Set G)) L)
    (iso : ClassicalGroup.IsPSL L 3 2) :
    Nonempty (inducedAutomizer V (L ⊓ M) ≃* Multiplicative (ZMod (2 ^ 1 - 1))) := by
  have he : inducedAutomizer V (L ⊓ M) = ⊥ :=
    (inducedAutomizer_eq_bot_iff (component_intersection_normalizes h hU hL.1)).mpr
      (binary_intersection_centralizes h hU hL iso)
  rw [he]
  change Nonempty ((⊥ : Subgroup (Automizer V)) ≃* Multiplicative (ZMod 1))
  let _ : Unique (Multiplicative (ZMod 1)) :=
    { default := 1, uniq := fun _ => Subsingleton.elim _ _ }
  exact ⟨MulEquiv.ofUnique⟩

/-- The quotient action retains exactly C_V(L), rather than a larger quotient-fixed kernel. -/
theorem quotientAction_ker (h : HypothesisE61 K T M V)
    (hU : U ∈ obstructionFamily M V)
    (hL : ComponentIn (centralizer (U : Set G)) L) :
    (quotientAction h hU hL).ker = (centralizer (L : Set G)).subgroupOf V := by
  let _ := BorelActions.component_quasisimple hL
  rw [quotientAction, MonoidHom.ker_comp_of_injective _ _
    (MulAut.quotient_center_injective (G := L)), componentAction_ker]


/-- The entire quotient Borel preserves the actual quotient image, including for trivial center. -/
theorem quotientAction_range_stable
    (h : HypothesisE61 K T M V) (hU : U ∈ obstructionFamily M V)
    (hL : ComponentIn (centralizer (U : Set G)) L)
    (S : Sylow 2 L) (hz : IsPGroup 2 (center L))
    (hplace : L ⊓ M = markedBorel L S)
    (b : L ⧸ center L)
    (hb : b ∈ normalizer ((S : Subgroup L).map (QuotientGroup.mk' (center L)) :
      Set (L ⧸ center L)))
    (a : MulAut (L ⧸ center L)) (ha : a ∈ (quotientAction h hU hL).range) :
    MulAut.conj b * a * (MulAut.conj b)⁻¹ ∈ (quotientAction h hU hL).range := by
  let q := QuotientGroup.mk' (center L)
  obtain ⟨l,rfl⟩ := QuotientGroup.mk'_surjective (center L) b
  have hN : (normalizer ((S : Subgroup L).map q : Set (L ⧸ center L))).comap q =
      normalizer (S : Set L) := by
    rw [comap_normalizer_eq_of_surjective _ (QuotientGroup.mk'_surjective _),
      comap_map_eq_self (show q.ker ≤ (S : Subgroup L) by
        simpa only [q, QuotientGroup.ker_mk'] using hz.le_sylow_of_normal S)]
    rfl
  have hl : l ∈ normalizer (S : Set L) := hN ▸ hb
  obtain ⟨v,rfl⟩ := ha
  have hm := componentAction_range_stable h hU hL S hplace l hl
    (componentAction h hU hL v) ⟨v,rfl⟩
  have he : quotientAut (center L) (MulAut.conj l) = MulAut.conj (q l) := by
    ext x
    obtain ⟨y,rfl⟩ := QuotientGroup.mk'_surjective (center L) x
    rw [quotientAut_apply_mk]
    simp only [MulAut.conj_apply, map_mul, map_inv]
    rfl
  have hi := mem_map_of_mem (quotientAut (center L)) hm
  rw [map_mul, map_mul, map_inv, he] at hi
  simpa only [quotientAction, MonoidHom.range_comp, MonoidHom.comp_apply] using hi

private theorem inner_image_eq_of_transitive {D : Type*} [Group D]
    (A : Subgroup (MulAut D)) (Z B : Subgroup D)
    (hne : A ≠ ⊥) (hle : A ≤ Z.map MulAut.conj)
    (hstable : ∀ b ∈ B, ∀ a ∈ A, MulAut.conj b * a * (MulAut.conj b)⁻¹ ∈ A)
    (htrans : ∀ z ∈ Z, z ≠ 1 → ∀ w ∈ Z, w ≠ 1 →
      ∃ b ∈ B, b * z * b⁻¹ = w) : A = Z.map MulAut.conj := by
  apply le_antisymm hle
  obtain ⟨⟨a,ha⟩,hane⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  have hane : a ≠ 1 := fun he => hane (Subtype.ext he)
  obtain ⟨z,hz,rfl⟩ := hle ha
  have hzne : z ≠ 1 := by
    intro he
    exact hane (he ▸ map_one MulAut.conj)
  rintro a ⟨w,hw,rfl⟩
  by_cases hw1 : w = 1
  · simp [hw1]
  obtain ⟨b,hb,hbw⟩ := htrans z hz hzne w hw hw1
  have hh := hstable b hb (MulAut.conj z) ha
  rw [← map_inv, ← map_mul, ← map_mul, hbw] at hh
  exact hh

/-- Conditional image identification: a nontrivial Borel-invariant image fills the Sylow center. -/
theorem componentAction_range_eq_inner_center
    (h : HypothesisE61 K T M V) (earlier : EarlierLocalFacts T)
    (hU : U ∈ obstructionFamily M V)
    (hL : ComponentIn (centralizer (U : Set G)) L)
    (S : Sylow 2 L)
    (hS : (S : Subgroup L).map L.subtype = L ⊓ sylowCentralizer (T : Subgroup G) V)
    (hplace : L ⊓ M = markedBorel L S)
    (hfixer : ∀ a : MulAut L, (∀ s ∈ S, a s = s) →
      ∃ z ∈ (center S).map (S : Subgroup L).subtype, a = MulAut.conj z)
    (htrans : ∀ z ∈ (center S).map (S : Subgroup L).subtype, z ≠ 1 →
      ∀ w ∈ (center S).map (S : Subgroup L).subtype, w ≠ 1 →
        ∃ b ∈ normalizer (S : Set L), b * z * b⁻¹ = w) :
    (componentAction h hU hL).range =
      ((center S).map (S : Subgroup L).subtype).map MulAut.conj := by
  apply inner_image_eq_of_transitive _ _ (normalizer (S : Set L))
    (componentAction_range_ne_bot h earlier hU hL) _
    (componentAction_range_stable h hU hL S hplace) htrans
  rintro a ⟨v,rfl⟩
  obtain ⟨z,hz,he⟩ := hfixer (componentAction h hU hL v)
    (componentAction_fixes_marked_sylow h hU hL S hS v)
  exact ⟨z,hz,he.symm⟩


/-- The same image identification in the faithful central quotient action. -/
theorem quotientAction_range_eq_inner_center
    (h : HypothesisE61 K T M V) (earlier : EarlierLocalFacts T)
    (hU : U ∈ obstructionFamily M V)
    (hL : ComponentIn (centralizer (U : Set G)) L)
    (S : Sylow 2 L) (hz : IsPGroup 2 (center L))
    (hS : (S : Subgroup L).map L.subtype = L ⊓ sylowCentralizer (T : Subgroup G) V)
    (hplace : L ⊓ M = markedBorel L S)
    (hfixer : ∀ (R : Sylow 2 (L ⧸ center L)) (a : MulAut (L ⧸ center L)),
      (∀ s ∈ R, a s = s) →
      ∃ z ∈ (center R).map (R : Subgroup (L ⧸ center L)).subtype, a = MulAut.conj z)
    (htrans : ∀ R : Sylow 2 (L ⧸ center L),
      ∀ z ∈ (center R).map (R : Subgroup (L ⧸ center L)).subtype, z ≠ 1 →
      ∀ w ∈ (center R).map (R : Subgroup (L ⧸ center L)).subtype, w ≠ 1 →
        ∃ b ∈ normalizer (R : Set (L ⧸ center L)), b * z * b⁻¹ = w) :
    let R := S.mapSurjective (f := QuotientGroup.mk' (center L))
      (QuotientGroup.mk'_surjective _)
    (quotientAction h hU hL).range =
      ((center R).map (R : Subgroup (L ⧸ center L)).subtype).map MulAut.conj := by
  let R := S.mapSurjective (f := QuotientGroup.mk' (center L))
    (QuotientGroup.mk'_surjective _)
  apply inner_image_eq_of_transitive _ _ (normalizer (R : Set (L ⧸ center L)))
    (quotientAction_range_ne_bot h earlier hU hL) _
    (quotientAction_range_stable h hU hL S hz hplace) (htrans R)
  rintro a ⟨v,rfl⟩
  obtain ⟨z,hz,he⟩ := hfixer R (quotientAction h hU hL v)
    (quotientAction_fixes_marked_sylow h hU hL S hS v)
  exact ⟨z,hz,he.symm⟩

private theorem inner_injective_of_center_eq_bot {D : Type*} [Group D]
    (hc : center D = ⊥) : Function.Injective (MulAut.conj : D →* MulAut D) := by
  rw [← MonoidHom.ker_eq_bot_iff]
  apply le_antisymm _ bot_le
  intro x hx
  have hh : x ∈ center D := mem_center_iff.mpr (fun y => by
    have he : x * y * x⁻¹ = y := DFunLike.congr_fun hx y
    exact (mul_inv_eq_iff_eq_mul.mp he).symm)
  exact hc ▸ hh

omit [Finite G] in
private theorem ordinary_center_eq_bot {n : ℕ}
    (iso : ClassicalGroup.IsPSL L 3 (2 ^ n)) : center L = ⊥ := by
  obtain ⟨F, _, _, _, ⟨e⟩⟩ := iso
  let _ := Atlas.sl_perfect (F := F) 3 (by decide)
  have hz : center (Matrix.ProjectiveSpecialLinearGroup (Fin 3) F) = ⊥ :=
    Group.IsPerfect.center_quotient_center_eq_bot (Matrix.SpecialLinearGroup (Fin 3) F)
  apply (center L).eq_bot_iff_forall.mpr
  intro x hx
  apply e.injective
  rw [map_one]
  have he : e x ∈ center (Matrix.ProjectiveSpecialLinearGroup (Fin 3) F) :=
    (centerCongr e ⟨x,hx⟩).property
  simpa only [hz,mem_bot] using he

/-- Exact ordinary corank from the two intrinsic model inputs, including n = 1. -/
theorem actionCorank_eq_of_sylow_fixer_and_transitivity
    (h : HypothesisE61 K T M V) (earlier : EarlierLocalFacts T)
    (hU : U ∈ obstructionFamily M V)
    (hL : ComponentIn (centralizer (U : Set G)) L)
    {n : ℕ} (hn : 1 ≤ n) (iso : ClassicalGroup.IsPSL L 3 (2 ^ n))
    (S : Sylow 2 L)
    (hS : (S : Subgroup L).map L.subtype = L ⊓ sylowCentralizer (T : Subgroup G) V)
    (hplace : L ⊓ M = markedBorel L S)
    (hfixer : ∀ a : MulAut L, (∀ s ∈ S, a s = s) →
      ∃ z ∈ (center S).map (S : Subgroup L).subtype, a = MulAut.conj z)
    (htrans : ∀ z ∈ (center S).map (S : Subgroup L).subtype, z ≠ 1 →
      ∀ w ∈ (center S).map (S : Subgroup L).subtype, w ≠ 1 →
        ∃ b ∈ normalizer (S : Set L), b * z * b⁻¹ = w) :
    n = actionCorank V L := by
  have hinj := inner_injective_of_center_eq_bot (ordinary_center_eq_bot iso)
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := iso
  rw [actionCorank_eq_log_range h hU hL,
    componentAction_range_eq_inner_center h earlier hU hL S hS hplace hfixer htrans,
    card_map_of_injective hinj, card_map_of_injective (S : Subgroup L).subtype_injective,
    Matrix.PSL3.LinearThree.card_center_sylow_of_equiv F (by omega) hF e S,
    Nat.log_pow (by decide : 1 < 2)]

/-- Exact cover corank from the two intrinsic quotient-model inputs; n = 2 gives the PSL₃(4) case. -/
theorem actionCorank_eq_of_quotient_sylow_fixer_and_transitivity
    (h : HypothesisE61 K T M V) (earlier : EarlierLocalFacts T)
    (hU : U ∈ obstructionFamily M V)
    (hL : ComponentIn (centralizer (U : Set G)) L)
    {n : ℕ} (hn : 1 ≤ n) (iso : ClassicalGroup.IsPSL (L ⧸ center L) 3 (2 ^ n))
    (S : Sylow 2 L) (hz : IsPGroup 2 (center L))
    (hS : (S : Subgroup L).map L.subtype = L ⊓ sylowCentralizer (T : Subgroup G) V)
    (hplace : L ⊓ M = markedBorel L S)
    (hfixer : ∀ (R : Sylow 2 (L ⧸ center L)) (a : MulAut (L ⧸ center L)),
      (∀ s ∈ R, a s = s) →
      ∃ z ∈ (center R).map (R : Subgroup (L ⧸ center L)).subtype, a = MulAut.conj z)
    (htrans : ∀ R : Sylow 2 (L ⧸ center L),
      ∀ z ∈ (center R).map (R : Subgroup (L ⧸ center L)).subtype, z ≠ 1 →
      ∀ w ∈ (center R).map (R : Subgroup (L ⧸ center L)).subtype, w ≠ 1 →
        ∃ b ∈ normalizer (R : Set (L ⧸ center L)), b * z * b⁻¹ = w) :
    n = actionCorank V L := by
  let _ := BorelActions.component_quasisimple hL
  have hinj := inner_injective_of_center_eq_bot
    (Group.IsPerfect.center_quotient_center_eq_bot L)
  let R := S.mapSurjective (f := QuotientGroup.mk' (center L))
    (QuotientGroup.mk'_surjective _)
  have him := quotientAction_range_eq_inner_center h earlier hU hL S hz hS hplace hfixer htrans
  change (quotientAction h hU hL).range =
    ((center R).map (R : Subgroup (L ⧸ center L)).subtype).map MulAut.conj at him
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := iso
  rw [actionCorank_eq_log_range h hU hL, ← quotientAction_range_card h hU hL, him,
    card_map_of_injective hinj, card_map_of_injective (R : Subgroup (L ⧸ center L)).subtype_injective,
    Matrix.PSL3.LinearThree.card_center_sylow_of_equiv F (by omega) hF e R,
    Nat.log_pow (by decide : 1 < 2)]


omit [Finite G] in
private theorem scalar_coordinates
    {F J : Type*} [Field F] [Group J]
    (a : V →* MulAut J) (j : ↥(L ⊓ M) →* J)
    (hnorm : L ⊓ M ≤ normalizer (V : Set G))
    (r : Multiplicative F →* J) (χ : ↥(L ⊓ M) →* Fˣ)
    (hr : Function.Injective r) (hi : Function.Injective (MulAut.conj : J →* MulAut J))
    (him : a.range = r.range.map MulAut.conj)
    (ha : ∀ (b : ↥(L ⊓ M)) (v : V), a (V.normalizerMonoidHom ⟨b, hnorm b.property⟩ v) =
      MulAut.conj (j b) * a v * (MulAut.conj (j b))⁻¹)
    (hc : ∀ (b : ↥(L ⊓ M)) (x : F), j b * r (Multiplicative.ofAdd x) * (j b)⁻¹ =
      r (Multiplicative.ofAdd ((χ b : F) * x))) :
    ∃ f : V →* Multiplicative F, Function.Surjective f ∧ f.ker = a.ker ∧
      ∀ (b : ↥(L ⊓ M)) (v : V), f (V.normalizerMonoidHom ⟨b, hnorm b.property⟩ v) =
        Multiplicative.ofAdd ((χ b : F) * (f v).toAdd) := by
  let φ := (MulAut.conj : J →* MulAut J).comp r
  have hφ : Function.Injective φ := hi.comp hr
  have him' : a.range = φ.range := by rw [MonoidHom.range_comp]; exact him
  let e : Multiplicative F ≃* φ.range :=
    MulEquiv.ofBijective φ.rangeRestrict
      ⟨fun x y he => hφ (congrArg Subtype.val he), φ.rangeRestrict_surjective⟩
  let f := e.symm.toMonoidHom.comp
    (a.codRestrict φ.range (fun v => him' ▸ (show a v ∈ a.range from ⟨v,rfl⟩)))
  have hf (v : V) : φ (f v) = a v :=
    congrArg Subtype.val (e.apply_symm_apply _)
  refine ⟨f, ?_, ?_, ?_⟩
  · intro x
    obtain ⟨v,hv⟩ := him'.symm ▸ (show φ x ∈ φ.range from ⟨x,rfl⟩)
    exact ⟨v, hφ ((hf v).trans hv)⟩
  · ext v
    change f v = 1 ↔ a v = 1
    rw [← hf v, ← φ.map_one, hφ.eq_iff]
  · intro b v
    apply hφ
    rw [hf, ha, ← hf v]
    change MulAut.conj (j b) * MulAut.conj (r (f v)) * (MulAut.conj (j b))⁻¹ = _
    rw [← map_inv, ← map_mul, ← map_mul]
    exact congrArg MulAut.conj (hc b (f v).toAdd)

omit [Finite G] in
private theorem scalar_fixed_space
    {F : Type*} [Field F] [Finite F] {n : ℕ} (hn : 1 < n)
    (hF : Nat.card F = 2 ^ n)
    (hnorm : L ⊓ M ≤ normalizer (V : Set G))
    (f : V →* Multiplicative F) (χ : ↥(L ⊓ M) →* Fˣ)
    (hχ : Function.Surjective χ)
    (hker : f.ker = (centralizer (L : Set G)).subgroupOf V)
    (hc : ∀ (b : ↥(L ⊓ M)) (v : V), f (V.normalizerMonoidHom ⟨b, hnorm b.property⟩ v) =
      Multiplicative.ofAdd ((χ b : F) * (f v).toAdd)) :
    V ⊓ centralizer ((L ⊓ M : Subgroup G) : Set G) =
      V ⊓ centralizer (L : Set G) := by
  apply le_antisymm _ (inf_le_inf_left V (centralizer_le inf_le_left))
  intro v hv
  refine ⟨hv.1, ?_⟩
  have hfix (b : ↥(L ⊓ M)) :
      V.normalizerMonoidHom ⟨b,hnorm b.property⟩ ⟨v,hv.1⟩ = ⟨v,hv.1⟩ := by
    apply Subtype.ext
    change (b : G) * v * (b : G)⁻¹ = v
    rw [mem_centralizer_iff.mp hv.2 b b.property, mul_inv_cancel_right]
  have hz : (f ⟨v,hv.1⟩).toAdd = 0 := by
    by_contra hz
    have hall (u : Fˣ) : u = 1 := by
      obtain ⟨b,rfl⟩ := hχ u
      have he := hc b ⟨v,hv.1⟩
      rw [hfix b] at he
      apply Units.ext
      apply mul_right_cancel₀ hz
      simpa only [one_mul, Units.val_one, toAdd_ofAdd] using
        (congrArg Multiplicative.toAdd he).symm
    have hcard : Nat.card Fˣ = 1 := Nat.card_eq_one_iff_exists.mpr ⟨1,hall⟩
    rw [Nat.card_units, hF] at hcard
    have hp : 2 ^ 1 < 2 ^ n := Nat.pow_lt_pow_right (by decide) hn
    simp only [pow_one] at hp
    omega
  have hm : (⟨v,hv.1⟩ : V) ∈ f.ker := hz
  rw [hker] at hm
  exact hm

private theorem scalar_action_kernel
    {F : Type*} [Field F]
    (h : HypothesisE61 K T M V) (hU : U ∈ obstructionFamily M V)
    (hL : ComponentIn (centralizer (U : Set G)) L)
    (f : V →* Multiplicative F) (χ : ↥(L ⊓ M) →* Fˣ)
    (hf : Function.Surjective f)
    (hker : f.ker = (centralizer (L : Set G)).subgroupOf V)
    (hc : ∀ (b : ↥(L ⊓ M)) (v : V), f (V.normalizerMonoidHom
      ⟨b, (component_intersection_normalizes h hU hL.1) b.property⟩ v) =
      Multiplicative.ofAdd ((χ b : F) * (f v).toAdd)) :
    (V.normalizerMonoidHom.comp
      (inclusion (component_intersection_normalizes h hU hL.1))).ker = χ.ker := by
  let ρ := V.normalizerMonoidHom.comp
    (inclusion (component_intersection_normalizes h hU hL.1))
  ext b
  change ρ b = 1 ↔ χ b = 1
  constructor
  · intro hb
    obtain ⟨v,hv⟩ := hf (Multiplicative.ofAdd (1 : F))
    have he := hc b v
    change f (ρ b v) = _ at he
    rw [hb] at he
    change f v = _ at he
    rw [hv] at he
    apply Units.ext
    simpa using (congrArg Multiplicative.toAdd he).symm
  · intro hb
    apply MulEquiv.ext
    intro v
    have he : f (ρ b v * v⁻¹) = 1 := by
      rw [map_mul, map_inv]
      change f (V.normalizerMonoidHom ⟨b,_⟩ v) * (f v)⁻¹ = 1
      rw [hc, hb]
      simp
    have hcv : (ρ b v * v⁻¹ : V) ∈ (centralizer (L : Set G)).subgroupOf V :=
      hker ▸ he
    -- Triviality on V/C_V(L) puts this displacement in both coprime factors.
    have hw : ((ρ b v * v⁻¹ : V) : G) ∈ ⁅V, L ⊓ M⁆ := by
      rw [commutator_comm V (L ⊓ M)]
      exact commutator_mem_commutator b.property v.property
    have hcf : ((ρ b v * v⁻¹ : V) : G) ∈
        V ⊓ centralizer ((L ⊓ M : Subgroup G) : Set G) :=
      ⟨(ρ b v * v⁻¹).property, centralizer_le inf_le_left hcv⟩
    have hone : ((ρ b v * v⁻¹ : V) : G) = 1 := by
      have hh : ((ρ b v * v⁻¹ : V) : G) ∈
          ⁅V, L ⊓ M⁆ ⊓ (V ⊓ centralizer ((L ⊓ M : Subgroup G) : Set G)) := ⟨hw,hcf⟩
      rw [(intersection_decomposition h hU hL).2.1] at hh
      exact hh
    exact mul_inv_eq_one.mp (Subtype.ext hone)

omit [Finite G] in
private theorem automizer_equiv_of_scalar_kernel
    {F : Type*} [Field F]
    (hnorm : L ⊓ M ≤ normalizer (V : Set G))
    (χ : ↥(L ⊓ M) →* Fˣ) (hχ : Function.Surjective χ)
    (hker : (V.normalizerMonoidHom.comp (inclusion hnorm)).ker = χ.ker) :
    Nonempty (inducedAutomizer V (L ⊓ M) ≃* Fˣ) := by
  let a : ↥(L ⊓ M) →* Automizer V :=
    V.normalizerMonoidHom.rangeRestrict.comp (inclusion hnorm)
  have him : a.range = inducedAutomizer V (L ⊓ M) := by
    ext x
    constructor
    · rintro ⟨b,rfl⟩
      exact ⟨⟨b,hnorm b.property⟩,b.property,rfl⟩
    · rintro ⟨b,hb,rfl⟩
      exact ⟨⟨b,hb⟩,rfl⟩
  have hk : a.ker = χ.ker := by
    change (V.normalizerMonoidHom.rangeRestrict.comp (inclusion hnorm)).ker = _
    rw [← MonoidHom.comap_ker, MonoidHom.ker_rangeRestrict]
    rw [← MonoidHom.comap_ker] at hker
    exact hker
  exact ⟨(MulEquiv.subgroupCongr him.symm).trans
    ((QuotientGroup.quotientKerEquivRange a).symm.trans
      ((QuotientGroup.quotientMulEquivOfEq hk).trans
        (QuotientGroup.quotientKerEquivOfSurjective χ hχ)))⟩

private theorem marked_scalar_calculations
    {F J : Type*} [Field F] [Finite F] [Group J] [Finite J]
    (h : HypothesisE61 K T M V) (hU : U ∈ obstructionFamily M V)
    (hL : ComponentIn (centralizer (U : Set G)) L)
    {n : ℕ} (hn : 1 ≤ n) (hF : Nat.card F = 2 ^ n)
    (e : J ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 3) F)
    (S : Sylow 2 L) (hplace : L ⊓ M = markedBorel L S)
    (q : L →* J) (hq : Function.Surjective q) (hqS : q.ker ≤ (S : Subgroup L))
    (a : V →* MulAut J)
    (hker : a.ker = (centralizer (L : Set G)).subgroupOf V)
    (hi : Function.Injective (MulAut.conj : J →* MulAut J))
    (him : let R := S.mapSurjective (f := q) hq
      a.range = ((center R).map (R : Subgroup J).subtype).map MulAut.conj)
    (ha : ∀ (b : ↥(L ⊓ M)) (v : V), a (V.normalizerMonoidHom
      ⟨b, (component_intersection_normalizes h hU hL.1) b.property⟩ v) =
      MulAut.conj (q ⟨b,b.property.1⟩) * a v * (MulAut.conj (q ⟨b,b.property.1⟩))⁻¹) :
    Nonempty (inducedAutomizer V (L ⊓ M) ≃* Multiplicative (ZMod (2 ^ n - 1))) ∧
      (1 < n → V ⊓ centralizer ((L ⊓ M : Subgroup G) : Set G) =
        V ⊓ centralizer (L : Set G)) := by
  let R := S.mapSurjective (f := q) hq
  obtain ⟨r,χ,hr,hrange,hχ,hconj,_⟩ :=
    Matrix.PSL3.LinearThree.RootScalars.exists_sylow_center_scalar_action F (by omega) hF e R
  have hN : (normalizer (R : Set J)).comap q = normalizer (S : Set L) := by
    change (normalizer ((S : Subgroup L).map q : Set J)).comap q = _
    rw [comap_normalizer_eq_of_surjective _ hq, comap_map_eq_self hqS]
    rfl
  let j : ↥(L ⊓ M) →* J := q.comp (inclusion inf_le_left)
  have hj (b : ↥(L ⊓ M)) : j b ∈ normalizer (R : Set J) := by
    have hb : (⟨b,b.property.1⟩ : L) ∈ normalizer (S : Set L) := by
      have hb : (b : G) ∈ markedBorel L S := by
        rw [← hplace]
        exact b.property
      obtain ⟨x,hx,hxb⟩ := hb
      have he : x = (⟨b,b.property.1⟩ : L) := Subtype.ext hxb
      exact he ▸ hx
    change (⟨b,b.property.1⟩ : L) ∈ (normalizer (R : Set J)).comap q
    exact hN.symm ▸ hb
  let jN : ↥(L ⊓ M) →* normalizer (R : Set J) := j.codRestrict _ hj
  have hjN : Function.Surjective jN := by
    intro b
    obtain ⟨x,hx⟩ := hq b
    have hxN : x ∈ normalizer (S : Set L) := by
      rw [← hN]
      change q x ∈ normalizer (R : Set J)
      rw [hx]
      exact b.property
    have hxB : (x : G) ∈ L ⊓ M := hplace.symm ▸ mem_map_of_mem L.subtype hxN
    exact ⟨⟨x,hxB⟩,Subtype.ext hx⟩
  let χB := χ.comp jN
  have hχB : Function.Surjective χB := hχ.comp hjN
  obtain ⟨f,hf,hfk,hfc⟩ := scalar_coordinates a j
    (component_intersection_normalizes h hU hL.1) r χB hr hi
    (by rw [hrange]; exact him) ha (fun b x => hconj (jN b) x)
  have hk : f.ker = (centralizer (L : Set G)).subgroupOf V := hfk.trans hker
  constructor
  · obtain ⟨ea⟩ := automizer_equiv_of_scalar_kernel
      (component_intersection_normalizes h hU hL.1) χB hχB
      (scalar_action_kernel h hU hL f χB hf hk hfc)
    exact ⟨ea.trans (Matrix.PSL3.LinearThree.RootScalars.unitsCyclicEquiv F hF)⟩
  · intro hn'
    exact scalar_fixed_space hn' hF (component_intersection_normalizes h hU hL.1)
      f χB hχB hk hfc

/-- The three marked-action conclusions in the ordinary PSL₃ branch of E.6.8.
The model fixer and scalar calculations are discharged, including at n = 1;
only the independently supplied Borel placement remains conditional. -/
theorem ordinary_calculations
    (h : HypothesisE61 K T M V) (earlier : EarlierLocalFacts T)
    (hU : U ∈ obstructionFamily M V)
    (hL : ComponentIn (centralizer (U : Set G)) L)
    {n : ℕ} (hn : 1 ≤ n) (iso : ClassicalGroup.IsPSL L 3 (2 ^ n))
    (S : Sylow 2 L)
    (hS : (S : Subgroup L).map L.subtype = L ⊓ sylowCentralizer (T : Subgroup G) V)
    (hplace : L ⊓ M = markedBorel L S) :
    Nonempty (inducedAutomizer V (L ⊓ M) ≃* Multiplicative (ZMod (2 ^ n - 1))) ∧
      n = actionCorank V L ∧
      (1 < n → V ⊓ centralizer ((L ⊓ M : Subgroup G) : Set G) =
        V ⊓ centralizer (L : Set G)) := by
  have hi := inner_injective_of_center_eq_bot (ordinary_center_eq_bot iso)
  have isoCopy := iso
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := isoCopy
  have hfixer := Matrix.PSL3.LinearThree.exists_sylow_center_conj_of_equiv
    F (by omega : 0 < n) hF e S
  have htrans := Matrix.PSL3.LinearThree.RootScalars.sylow_center_nonidentity_transitive
    F (by omega : 0 < n) hF e S
  have hdim := actionCorank_eq_of_sylow_fixer_and_transitivity
    h earlier hU hL hn iso S hS hplace hfixer htrans
  have him := componentAction_range_eq_inner_center h earlier hU hL S hS hplace hfixer htrans
  have hid : S.mapSurjective (f := MonoidHom.id L) Function.surjective_id = S := by
    apply Sylow.ext
    change (S : Subgroup L).map (MonoidHom.id L) = (S : Subgroup L)
    exact map_id _
  obtain ⟨hact,hfixed⟩ := marked_scalar_calculations h hU hL hn hF e S hplace
    (MonoidHom.id L) Function.surjective_id (by simp)
    (componentAction h hU hL) (componentAction_ker h hU hL) hi
    (by dsimp only; rw [hid]; exact him) (componentAction_conjugate h hU hL)
  exact ⟨hact,hdim,hfixed⟩

/-- The three marked-action conclusions for a perfect central two-cover of PSL₃.
No nontriviality assumption on the covering center is made. The source case
is n = 2, supplied separately below. -/
theorem central_quotient_calculations
    (h : HypothesisE61 K T M V) (earlier : EarlierLocalFacts T)
    (hU : U ∈ obstructionFamily M V)
    (hL : ComponentIn (centralizer (U : Set G)) L)
    {n : ℕ} (hn : 1 ≤ n) (iso : ClassicalGroup.IsPSL (L ⧸ center L) 3 (2 ^ n))
    (S : Sylow 2 L) (hz : IsPGroup 2 (center L))
    (hS : (S : Subgroup L).map L.subtype = L ⊓ sylowCentralizer (T : Subgroup G) V)
    (hplace : L ⊓ M = markedBorel L S) :
    Nonempty (inducedAutomizer V (L ⊓ M) ≃* Multiplicative (ZMod (2 ^ n - 1))) ∧
      n = actionCorank V L ∧
      (1 < n → V ⊓ centralizer ((L ⊓ M : Subgroup G) : Set G) =
        V ⊓ centralizer (L : Set G)) := by
  let _ := BorelActions.component_quasisimple hL
  have hi := inner_injective_of_center_eq_bot
    (Group.IsPerfect.center_quotient_center_eq_bot L)
  have isoCopy := iso
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := isoCopy
  have hfixer := Matrix.PSL3.LinearThree.exists_sylow_center_conj_of_equiv
    F (by omega : 0 < n) hF e
  have htrans := Matrix.PSL3.LinearThree.RootScalars.sylow_center_nonidentity_transitive
    F (by omega : 0 < n) hF e
  have hdim := actionCorank_eq_of_quotient_sylow_fixer_and_transitivity
    h earlier hU hL hn iso S hz hS hplace hfixer htrans
  have him := quotientAction_range_eq_inner_center h earlier hU hL S hz hS hplace hfixer htrans
  let q := QuotientGroup.mk' (center L)
  have he (l : L) : quotientAut (center L) (MulAut.conj l) = MulAut.conj (q l) := by
    ext x
    obtain ⟨y,rfl⟩ := QuotientGroup.mk'_surjective (center L) x
    rw [quotientAut_apply_mk]
    simp only [MulAut.conj_apply, map_mul, map_inv]
    rfl
  have ha (b : ↥(L ⊓ M)) (v : V) :
      quotientAction h hU hL
        (V.normalizerMonoidHom ⟨b, component_intersection_normalizes h hU hL.1 b.property⟩ v) =
      MulAut.conj (q ⟨b,b.property.1⟩) * quotientAction h hU hL v *
        (MulAut.conj (q ⟨b,b.property.1⟩))⁻¹ := by
    have hh := congrArg (quotientAut (center L)) (componentAction_conjugate h hU hL b v)
    simpa only [quotientAction, MonoidHom.comp_apply, map_mul, map_inv, he] using hh
  obtain ⟨hact,hfixed⟩ := marked_scalar_calculations h hU hL hn hF e S hplace
    q (QuotientGroup.mk'_surjective _)
    (by simpa only [q, QuotientGroup.ker_mk'] using hz.le_sylow_of_normal S)
    (quotientAction h hU hL) (quotientAction_ker h hU hL) hi him ha
  exact ⟨hact,hdim,hfixed⟩

/-- The literal PSL₃(4) central-cover action clause of E.6.8 after marked Borel
placement, with the fixed-space equality specialized to n = 2. -/
theorem four_cover_calculations
    (h : HypothesisE61 K T M V) (earlier : EarlierLocalFacts T)
    (hU : U ∈ obstructionFamily M V)
    (hL : ComponentIn (centralizer (U : Set G)) L)
    (iso : ClassicalGroup.IsPSL (L ⧸ center L) 3 4)
    (S : Sylow 2 L) (hz : IsPGroup 2 (center L))
    (hS : (S : Subgroup L).map L.subtype = L ⊓ sylowCentralizer (T : Subgroup G) V)
    (hplace : L ⊓ M = markedBorel L S) :
    Nonempty (inducedAutomizer V (L ⊓ M) ≃* Multiplicative (ZMod (2 ^ 2 - 1))) ∧
      2 = actionCorank V L ∧
      V ⊓ centralizer ((L ⊓ M : Subgroup G) : Set G) =
        V ⊓ centralizer (L : Set G) := by
  obtain ⟨ha,hd,hf⟩ := central_quotient_calculations
    h earlier hU hL (n := 2) (by decide) iso S hz hS hplace
  exact ⟨ha,hd,hf (by decide)⟩

end CFSG.Quasithin.ChapterE.Section06.Components.LieSieve.LinearThree.MarkedAction
