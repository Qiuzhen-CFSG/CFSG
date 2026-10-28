module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.RootCoordinates.SimplePanels
public import Theory.GroupAction.CartanPanelFixedPoints
public import Theory.GroupTheory.Commutator.FixedPointFree

/-!
# Actual Cartan complements and simple-root containment

If A is normalized by the entire Borel B = UH, its intersection with B
splits over A ∩ U with the actual complement A ∩ H. In B/(A ∩ B),
the images of the two factors have coprime orders and therefore intersect
trivially. This proves the factorization without choosing a new torus.

A normal subgroup supplement identifies its own Borel cosets equivariantly
with the full endpoint panel, even though it need not be the entire endpoint.
The literal root chart r ↦ r nᵢ B then converts an element of H with exactly
two fixed panel cosets into a fixed-point-free automorphism of the simple
root. The finite commutator lemma places that root inside the normal factor.

These are local steps towards the both-perfect reduction in DGS, Groups and
Graphs, Part II, pp.80–81 and Theorem D, p.224. They use the proved simple
Bruhat chart, not a Lie-model identification or a restricted BN-pair.
-/

public noncomputable section
open Subgroup
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary
variable {X : Type*} [Group X] [Finite X] {T : TitsSystem (X := X)}
  (split : SplitData T)

theorem normal_borel_intersection_factorization (A : Subgroup X)
    (hn : T.B ≤ normalizer (A : Set X)) :
    (A ⊓ split.U) ⊔ (A ⊓ (T.B ⊓ T.N)) = A ⊓ T.B := by
  let J := A.subgroupOf T.B
  let U := split.U.subgroupOf T.B
  let H := (T.B ⊓ T.N).subgroupOf T.B
  let : J.Normal := normal_subgroupOf_of_le_normalizer hn
  let : U.Normal := normal_subgroupOf_of_le_normalizer split.normalizes
  let q := QuotientGroup.mk' J
  have ho : Nat.Coprime 2 (Nat.card H) := by
    rw [Nat.card_congr (subgroupOfEquivOfLe (show T.B ⊓ T.N ≤ T.B from inf_le_left)).toEquiv]
    exact split.odd
  have hd : Disjoint (U.map q) (H.map q) := by
    obtain ⟨k,hk⟩ := (split.isTwo.comap_subtype.map q).exists_card_eq
    apply disjoint_of_coprime_natCard
    change Nat.card (U.map q) = 2 ^ k at hk
    rw [hk]
    exact (ho.of_dvd_right (H.card_map_dvd q)).pow_left k
  have hUH : U ⊔ H = ⊤ := by
    rw [← subgroupOf_sup split.U_le inf_le_left, split.factorization, subgroupOf_self]
  apply le_antisymm (sup_le (inf_le_inf_left _ split.U_le)
    (inf_le_inf_left _ inf_le_left))
  intro a ha
  let b : T.B := ⟨a,ha.2⟩
  obtain ⟨u,hu,v,hv,he⟩ := mem_sup_of_normal_left.mp (hUH ▸ mem_top b)
  have hqa : q b = 1 := (QuotientGroup.eq_one_iff (N := J) b).mpr ha.1
  have hqu : q u = (q v)⁻¹ := by
    apply mul_eq_one_iff_eq_inv.mp
    rw [← map_mul, he, hqa]
  have hqzero : q u = 1 := (disjoint_def.mp hd) (mem_map_of_mem q hu)
    (hqu ▸ (H.map q).inv_mem (mem_map_of_mem q hv))
  have huA : (u : X) ∈ A := (QuotientGroup.eq_one_iff (N := J) u).mp hqzero
  have hvA : (v : X) ∈ A := by
    have h := A.mul_mem (A.inv_mem huA) ha.1
    have he' : (u : X) * v = a := congrArg Subtype.val he
    rw [← he', inv_mul_cancel_left] at h
    exact h
  have hm := mul_mem_sup (show (u : X) ∈ A ⊓ split.U from ⟨huA,hu⟩)
    (show (v : X) ∈ A ⊓ (T.B ⊓ T.N) from ⟨hvA,hv⟩)
  rwa [← Subgroup.coe_mul, he] at hm

end Theory.AlgebraicGroup.TitsSystem.SourceBinary

public noncomputable section
open Subgroup Theory.CartanPanel
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary
variable {G H : Type*} [Group G] [Group H]

/-- A normal subgroup supplement acts transitively on the full Borel coset space. -/
theorem cosetMap_bijective_of_normal_range (f : G →* H) (B : Subgroup G) (C : Subgroup H)
    (hBC : C.comap f = B) (hn : f.range.Normal) (hgen : f.range ⊔ C = ⊤) :
    Function.Bijective (cosetMap f B C hBC) := by
  let := hn
  refine ⟨cosetMap_injective f B C hBC, ?_⟩
  intro y
  induction y using Quotient.inductionOn with | h y =>
    obtain ⟨a, ha, b, hb, he⟩ := mem_sup_of_normal_left.mp (hgen ▸ mem_top y)
    obtain ⟨x, rfl⟩ := ha
    refine ⟨QuotientGroup.mk x, ?_⟩
    rw [cosetMap_mk]
    apply QuotientGroup.eq.mpr
    rw [← he, inv_mul_cancel_left]
    exact hb

def supplementCosetEquiv (f : G →* H) (B : Subgroup G) (C : Subgroup H)
    (hBC : C.comap f = B) (hn : f.range.Normal) (hgen : f.range ⊔ C = ⊤) :
    G ⧸ B ≃ H ⧸ C :=
  Equiv.ofBijective (cosetMap f B C hBC)
    (cosetMap_bijective_of_normal_range f B C hBC hn hgen)

@[simp] theorem supplementCosetEquiv_mk (f : G →* H) (B : Subgroup G) (C : Subgroup H)
    (hBC : C.comap f = B) (hn : f.range.Normal) (hgen : f.range ⊔ C = ⊤) (g : G) :
    supplementCosetEquiv f B C hBC hn hgen (QuotientGroup.mk g) =
      QuotientGroup.mk (f g) := by rfl

theorem supplementCosetEquiv_smul (f : G →* H) (B : Subgroup G) (C : Subgroup H)
    (hBC : C.comap f = B) (hn : f.range.Normal) (hgen : f.range ⊔ C = ⊤)
    (g : G) (ω : G ⧸ B) :
    supplementCosetEquiv f B C hBC hn hgen (g • ω) =
      f g • supplementCosetEquiv f B C hBC hn hgen ω := by
  induction ω using Quotient.inductionOn with | h x =>
    change QuotientGroup.mk (f (g * x)) = QuotientGroup.mk (f g * f x)
    rw [map_mul]

/-- The fixed-pair statement passes to the literal larger endpoint panel,
although the homomorphism need not be surjective on groups. -/
theorem two_fixed_pushforward_of_normal_range (f : G →* H) (B : Subgroup G)
    (C : Subgroup H) (hBC : C.comap f = B) (hn : f.range.Normal)
    (hgen : f.range ⊔ C = ⊤) (D : Subgroup G) (h : HasTwoFixedCosets B D) :
    HasTwoFixedCosets C (D.map f) := by
  obtain ⟨d, hd, β, hβ, hfix⟩ := h
  let e := supplementCosetEquiv f B C hBC hn hgen
  have hone : e (QuotientGroup.mk 1) = QuotientGroup.mk 1 := by simp [e]
  refine ⟨f d, mem_map_of_mem f hd, e β, ?_, ?_⟩
  · intro he
    exact hβ (e.injective (he.trans hone.symm))
  · intro ω
    obtain ⟨v, rfl⟩ := e.surjective ω
    rw [← supplementCosetEquiv_smul, e.injective.eq_iff, hfix]
    exact or_congr
      ⟨fun hv => by rw [hv, hone], fun hv => e.injective (hv.trans hone.symm)⟩
      ⟨fun hv => congrArg e hv, fun hv => e.injective hv⟩
end Theory.AlgebraicGroup.TitsSystem.SourceBinary

public noncomputable section
open Subgroup
open Theory.CartanPanel
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary
open RootCoordinates
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits)

theorem simpleRoot_fixedPointFree_of_two_fixed_cosets (i : Fin 2)
    (d : X ⧸ Q.D) (hd : d ∈ Q.tits.B ⊓ Q.tits.N)
    (β : Panel Q i) (_hβ : β ≠ QuotientGroup.mk 1)
    (hfix : ∀ ω : Panel Q i,
      (⟨d, Q.tits.B_le_standardParabolic _ hd.1⟩ :
        Q.tits.standardParabolic {Q.simple i}) • ω = ω ↔
      ω = QuotientGroup.mk 1 ∨ ω = β) :
    ∀ r ∈ simpleRoot Q split i, Commute d r → r = 1 := by
  let n := representative (Q.simple i)
  let hn := representative_spec (Q.simple i)
  let chart := simplePanelMap Q split i n hn
  have hnP : (n : X ⧸ Q.D) ∈ Q.tits.standardParabolic {Q.simple i} :=
    Q.tits.bruhatCell_subset_standardParabolic_of_mem (Set.mem_singleton _)
      (Q.tits.representative_mem_bruhatCell _ n hn)
  let nP : Q.tits.standardParabolic {Q.simple i} := ⟨n, hnP⟩
  let base : Panel Q i := QuotientGroup.mk nP
  let dP : Q.tits.standardParabolic {Q.simple i} :=
    ⟨d, Q.tits.B_le_standardParabolic _ hd.1⟩
  have hformula (r : simpleRoot Q split i) :
      (chart r).val = QuotientGroup.mk
        (⟨(r : X ⧸ Q.D) * n,
          (Q.tits.standardParabolic {Q.simple i}).mul_mem
            (Q.tits.B_le_standardParabolic _ (split.U_le r.property.1)) hnP⟩ :
          Q.tits.standardParabolic {Q.simple i}) :=
    simplePanelMap_apply Q split i n hn r _
  have hne (r : simpleRoot Q split i) : (chart r).val ≠ QuotientGroup.mk 1 := by
    intro he
    rw [hformula] at he
    have hm := QuotientGroup.eq.mp he.symm
    change (1 : X ⧸ Q.D)⁻¹ * ((r : X ⧸ Q.D) * n) ∈ Q.tits.B at hm
    simp only [inv_one, one_mul] at hm
    have hnB : (n : X ⧸ Q.D) ∈ Q.tits.B := by
      simpa only [inv_mul_cancel_left] using
        Q.tits.B.mul_mem (Q.tits.B.inv_mem (split.U_le r.property.1)) hm
    have hq := (QuotientGroup.eq_one_iff n).mpr
      (show n ∈ (Q.tits.B ⊓ Q.tits.N).subgroupOf Q.tits.N from ⟨hnB,n.property⟩)
    exact (Q.tits.involutions _ (Q.simple_mem i)).1 (hn.symm.trans hq)
  have hchart1 : (chart 1).val = base := by
    rw [hformula]
    congr 1
    exact Subtype.ext (one_mul _)
  have hbase : dP • base = base := by
    change QuotientGroup.mk (dP * nP) = QuotientGroup.mk nP
    apply QuotientGroup.eq.mpr
    change (d * (n : X ⧸ Q.D))⁻¹ * n ∈ Q.tits.B
    have hc := (mem_normalizer_iff.mp (torus_normalizes n⁻¹) d⁻¹).mp
      ((Q.tits.B ⊓ Q.tits.N).inv_mem hd)
    have hcB : ((n⁻¹ : Q.tits.N) : X ⧸ Q.D) * d⁻¹ *
        (((n⁻¹ : Q.tits.N) : X ⧸ Q.D))⁻¹ ∈ Q.tits.B := hc.1
    simpa only [Subgroup.coe_inv, mul_inv_rev, mul_assoc, one_mul, inv_inv] using hcB
  have hbaseβ : base = β := ((hfix base).mp hbase).resolve_left (hchart1 ▸ hne 1)
  intro r hr hcomm
  let rP : Q.tits.standardParabolic {Q.simple i} :=
    ⟨r, Q.tits.B_le_standardParabolic _ (split.U_le hr.1)⟩
  have hcommP : dP * rP = rP * dP := Subtype.ext hcomm.eq
  have hchart : (chart ⟨r,hr⟩).val = rP • base := by
    rw [hformula]
    rfl
  have hf : dP • (chart ⟨r,hr⟩).val = (chart ⟨r,hr⟩).val := by
    rw [hchart, ← mul_smul, hcommP, mul_smul, hbase]
  have he := ((hfix _).mp hf).resolve_left (hne ⟨r,hr⟩)
  have he' : chart ⟨r,hr⟩ = chart 1 := Subtype.ext (he.trans (hbaseβ.symm.trans hchart1.symm))
  exact congrArg Subtype.val (simplePanelMap_injective Q split i n hn he')

theorem simpleRoot_le_of_two_fixed_cosets (i : Fin 2)
    (A : Subgroup (X ⧸ Q.D))
    (hnormal : Q.tits.standardParabolic {Q.simple i} ≤ normalizer (A : Set (X ⧸ Q.D)))
    (hfix : HasTwoFixedCosets
      (Q.tits.B.subgroupOf (Q.tits.standardParabolic {Q.simple i}))
      ((A ⊓ (Q.tits.B ⊓ Q.tits.N)).subgroupOf
        (Q.tits.standardParabolic {Q.simple i}))) :
    simpleRoot Q split i ≤ A := by
  obtain ⟨d, hd, β, hβ, hfix⟩ := hfix
  have hdH : (d : X ⧸ Q.D) ∈ Q.tits.B ⊓ Q.tits.N := hd.2
  have hf := simpleRoot_fixedPointFree_of_two_fixed_cosets Q split i d hdH β hβ hfix
  let D := A ⊓ (Q.tits.B ⊓ Q.tits.N)
  have he : ⁅simpleRoot Q split i, D⁆ = simpleRoot Q split i :=
    Theory.GroupTheory.commutator_eq_of_fixedPointFree _ _
      (inf_le_right.trans (torus_normalizes_simpleRoot Q split i)) d hd hf
  rw [← he]
  exact (commutator_mono le_rfl inf_le_left).trans
    (le_normalizer_iff_commutator_le_right.mp
      ((simpleRoot_le Q split i).trans (split.U_le.trans
        ((Q.tits.B_le_standardParabolic _).trans hnormal))))

end Theory.AlgebraicGroup.TitsSystem.SourceBinary
