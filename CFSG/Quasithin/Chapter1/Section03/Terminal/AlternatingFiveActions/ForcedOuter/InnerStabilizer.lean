module

public import CFSG.Quasithin.Chapter1.Section03.Terminal.AlternatingFiveActions.ForcedOuter.OddLine
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.Swapped.Sylow
public import Theory.SpecificGroups.AlternatingFiveSolvableSylow


/-!
# Inner stabilizers centralize the actual odd intersection

Let A be the image of P ∩ B in B/O₂(B), identified with A₅. Restrict the
specified Sylow subgroup to B and project it to a Sylow four-group Q.
The actual solvable subgroup (XT ∩ B) projects to a solvable overgroup
of Q and A, so A normalizes Q. The image of T ∩ N_G(B) in the quotient
automorphism group is a two-group containing Inn(Q). Sylow maximality
therefore puts every inner conjugator from that image in Q.

An actor also normalizing P stabilizes A. Its displacements lie in both
Q and the odd subgroup A, so they vanish. Injectivity of the actual
quotient map on P ∩ B lifts this to centralization in G. This argument
works for every odd p and requires no assumed outer actor or model action.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
combined manuscript of 1 March 2004, final paragraph of Lemma 1.3.9(1),
printed p.514, PDF p.531.
-/

@[expose] public section

open Subgroup
namespace CFSG.Quasithin.Chapter1.Terminal.ForcedOuter
open XiEmbedding
variable {G : Type*} [Group G] [Finite G]
variable {p : ℕ} {T X P H B : Subgroup G}

/-- Inner component-stabilizing actors centralize P ∩ B, using the actual restricted Sylow subgroup. -/
theorem inner_stabilizer_centralizes_of_sylow
    (h : LocalInput p T X P H) (hS : IsSylowIn 2 (T ⊓ B) B)
    (e : XiQuotient B ≃* alternatingGroup (Fin 5)) :
    ((T ⊓ normalizer P) ⊓ normalizer B) ⊓ innerTwoQuotientNormalizer B ≤
      centralizer (P ⊓ B : Set G) := by
  let _ : Fact p.Prime := ⟨h.prime⟩
  obtain ⟨S, hS⟩ := hS
  let q := QuotientGroup.mk' (pCore 2 B)
  let Q : Sylow 2 (XiQuotient B) := S.mapSurjective (f := q) (QuotientGroup.mk'_surjective _)
  let D := T ⊓ normalizer B
  let f : D →* MulAut (XiQuotient B) :=
    (twoQuotientNormalizerAction B).comp (inclusion inf_le_right)
  let R := f.range
  have hR : IsPGroup 2 R := h.two_group.to_inf_left.of_surjective
    f.rangeRestrict f.rangeRestrict_surjective
  have hST (b : B) (hb : b ∈ S) : (b : G) ∈ T := by
    have hh : (b : G) ∈ T ⊓ B := hS ▸ mem_map_of_mem B.subtype hb
    exact hh.1
  have hQR : (Q : Subgroup (XiQuotient B)).map MulAut.conj ≤ R := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨b, hb, rfl⟩ := hx
    let bD : D := ⟨b, hST b hb, B.le_normalizer b.property⟩
    exact ⟨bD, quotient_action_component b⟩
  let I := (X ⊔ T).subgroupOf B
  let J := I.map q
  let A := (P.subgroupOf B).map q
  have hI : Group.IsSolvable I := by
    let _ := SwappedSylow.local_solvable h
    apply Group.isSolvable_of_isSolvable_injective (f := B.subtype.subgroupComap (X ⊔ T))
    intro a b he
    exact Subtype.ext (Subtype.ext (congrArg (fun z : (X ⊔ T : Subgroup G) => (z : G)) he))
  have hJ : Group.IsSolvable J := Group.isSolvable_of_surjective (q.subgroupMap_surjective I)
  have hQJ : (Q : Subgroup (XiQuotient B)) ≤ J := by
    apply map_mono
    intro b hb
    exact (show T ≤ X ⊔ T from le_sup_right) (hST b hb)
  have hAJ : A ≤ J := map_mono (fun b hb => (h.complement_le.trans le_sup_left) hb)
  have hn : A ≤ normalizer (Q : Set (XiQuotient B)) := hAJ.trans
    (alternatingGroup.solvable_sylow_overgroup_le_normalizer_of_equiv e Q J hQJ)
  have hA : IsPGroup p A := h.odd_complement.isPGroup.comap_subtype.map q
  have hd : Disjoint (Q : Subgroup (XiQuotient B)) A :=
    Q.isPGroup'.disjoint_of_coprime hA h.odd.coprime_two_left
  have hz : center (XiQuotient B) = ⊥ := by
    apply bot_unique
    intro z hz
    have he : e z ∈ center (alternatingGroup (Fin 5)) := by
      apply mem_center_iff.mpr
      intro y
      obtain ⟨x, rfl⟩ := e.surjective y
      rw [← map_mul, ← map_mul]
      exact congrArg e (mem_center_iff.mp hz x)
    rw [alternatingGroup.center_eq_bot (by simp)] at he
    exact e.injective ((mem_bot.mp he).trans e.map_one.symm)
  intro s hs
  let sD : D := ⟨s, hs.1.1.1, hs.1.2⟩
  have hβ : f sD ∈ R := ⟨sD, rfl⟩
  have hi : ∃ b, f sD = MulAut.conj b :=
    quotient_action_inner_of_mem_innerNormalizer ⟨s, hs.1.2⟩ hs.2
  have hstable : ∀ a ∈ A, f sD a ∈ A := by
    rintro _ ⟨a, ha, rfl⟩
    change twoQuotientNormalizerAction B ⟨s, hs.1.2⟩ (q a) ∈ A
    rw [twoQuotientNormalizerAction_mk]
    apply mem_map_of_mem q
    exact (mem_normalizer_iff.mp hs.1.1.2 (a : G)).mp ha
  have hfix := MulAut.inner_actor_fixes_disjoint_subgroup hz Q R hR hQR A hd hn hβ hi hstable
  apply centralizes_oddLine_of_quotient_fixes h.odd h.odd_complement.isPGroup hs.1.1.2 hs.1.2
  intro a ha
  exact hfix (q a) (mem_map_of_mem q ha)

universe u
variable {𝒦 : GroupClass.{u}} {G₀ : Type u} [Group G₀] [Finite G₀]
variable {T₀ X₀ P₀ H₀ B₀ : Subgroup G₀}

/-- The genuine source hypotheses discharge every premise of the inner-stabilizer calculation. -/
theorem SourceInput.inner_stabilizer_centralizes
    (h : SourceInput 𝒦 p T₀ X₀ P₀ H₀ B₀) :
    ((T₀ ⊓ normalizer P₀) ⊓ normalizer B₀) ⊓ innerTwoQuotientNormalizer B₀ ≤
      centralizer (P₀ ⊓ B₀ : Set G₀) := by
  exact inner_stabilizer_centralizes_of_sylow h.toLocalInput
    (Section02.IndexTwo.isSylowIn_inf_of_subnormal h.sylow_two h.component.1
      h.component.2.subnormal) h.alternating_five.some

end CFSG.Quasithin.Chapter1.Terminal.ForcedOuter
