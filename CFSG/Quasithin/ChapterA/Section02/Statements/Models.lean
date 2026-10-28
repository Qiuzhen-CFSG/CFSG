module

public import CFSG.Quasithin.ClassificationModels.RankTwo
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.McL

/-!
# The actual model lists in Theorems B and C

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
manuscript of 1 March 2004, A.2.2–A.2.4, printed p.33 (PDF p.44).

These are output definitions, not classification theorems. Every alternative
contains an actual multiplicative equivalence. The characteristic-two families
reuse the shared classification carriers, including the genuine triality and
Ree constructions and the small derived groups. Lie rank is relative rank;
unitary q is the fixed-field order, so U₅(4) uses matrices over order 16.
C omits the U₄ and U₅ families and the sporadics J₃ and McL. In particular the
thirteen-sporadic B list differs from the eleven-sporadic Main Theorem list:
B also includes J₁ and McL, whereas C includes J₁ and omits J₃.

The source's implicit field and nonabelian-simple conventions accompany these
lists in `Statements`. Field witnesses rule out exponent zero. We retain the
displayed upper bounds on alternating degree and field exponent. The bridges
below compose equivalences and include each C alternative in its B alternative;
they require no order, simplicity, or classification certificates for the models.
-/

@[expose] public section

universe u v

namespace CFSG.Quasithin.ChapterA.Section02

open ClassificationModels

/-- A nonprojective special unitary group, with q the fixed-field order.
This is the group SU, not PSU, needed for A(1.b). -/
def IsSpecialUnitaryModel (G : Type u) [Group G] (n q : ℕ) : Prop :=
  ∃ (F : Type) (_ : Field F) (_ : Finite F)
      (J : BenderSuzuki.MatrixGroups.HermitianForm n F),
    Nat.card F = q ^ 2 ∧ (∀ x, J.conj x = x ^ q) ∧
      Nonempty (G ≃* J.specialSubgroup)

/-- The exact odd-characteristic alternatives B(2).
The Fermat and Mersenne restrictions apply to different dimension-four families. -/
inductive IsTheoremBOddModel (G : Type u) [Group G] : Prop
  | linear_two (q : ℕ) (hq : Odd q) (iso : ClassicalGroup.IsPSL G 2 q)
  | linear_three (p e : ℕ) (hp : p.Prime) (ho : Odd p) (he : e ≤ 2)
      (iso : ClassicalGroup.IsPSL G 3 (p ^ e))
  | unitary_three (p e : ℕ) (hp : p.Prime) (ho : Odd p) (he : e ≤ 2)
      (iso : ClassicalGroup.IsPSU G 3 (p ^ e))
  | symplectic (p : ℕ) (hp : p.Prime) (ho : Odd p)
      (iso : ClassicalGroup.IsPSp G 2 p)
  | g2 (p : ℕ) (hp : p.Prime) (ho : Odd p) (iso : IsG2At G p)
  | linear_four (r : ℕ) (hp : r.Prime) (hf : ∃ k : ℕ, r = 2 ^ (2 ^ k) + 1)
      (iso : ClassicalGroup.IsPSL G 4 r)
  | unitary_four (s : ℕ) (hp : s.Prime) (hm : ∃ b : ℕ, s + 1 = 2 ^ b)
      (iso : ClassicalGroup.IsPSU G 4 s)

/-- The exact odd-characteristic alternatives C(2). -/
inductive IsTheoremCOddModel (G : Type u) [Group G] : Prop
  | linear_two (p e : ℕ) (hp : p.Prime) (ho : Odd p) (he : e ≤ 2)
      (iso : ClassicalGroup.IsPSL G 2 (p ^ e))
  | linear_three (p : ℕ) (hp : p.Prime) (ho : Odd p)
      (iso : ClassicalGroup.IsPSL G 3 p)
  | unitary_three (p : ℕ) (hp : p.Prime) (ho : Odd p)
      (iso : ClassicalGroup.IsPSU G 3 p)

/-- The rank-two part of C(3), as enumerated in A.2.4. Unlike B(3), this
contains neither the dimension-four nor dimension-five unitary family. -/
inductive IsTheoremCRankTwoModel (G : Type u) [Group G] (f : ℕ) : Prop
  | linear (hf : 1 ≤ f) (iso : ClassicalGroup.IsPSL G 3 (2 ^ f))
  | symplectic (hf : 2 ≤ f) (iso : ClassicalGroup.IsPSp G 2 (2 ^ f))
  | g2 (hf : 2 ≤ f) (iso : IsG2At G (2 ^ f))
  | triality (hf : 1 ≤ f) (iso : Triality.Standard.IsTrialityGroupAt (2 ^ f) G)
  | ree_f4 (m : ℕ) (hm : 1 ≤ m) (hf : f = 2 * m + 1)
      (iso : Nonempty (G ≃* ReeF4.Model m))
  | symplectic_derived (hf : f = 1)
      (iso : Nonempty (G ≃* commutator (ClassicalGroup.PSp 2 (ZMod 2))))
  | g2_derived (hf : f = 1)
      (iso : Nonempty (G ≃* commutator (Atlas.G2.Model (ZMod 2))))
  | tits (hf : f = 1) (iso : Nonempty (G ≃* Tits.ParrottGroup))

/-- B(5): five Mathieu groups, all four Janko groups, HS, He, Ru, and McL. -/
def IsTheoremBSporadicModel (G : Type u) [Group G] : Prop :=
  IsSporadicModel G ∨ Nonempty (G ≃* Janko1.Model) ∨
    Nonempty (G ≃* Sporadic.LeechRelated.McL.Carrier)

/-- C(5): five Mathieu groups, J₁, J₂, J₄, HS, He, and Ru. -/
def IsTheoremCSporadicModel (G : Type u) [Group G] : Prop :=
  (∃ name : SporadicName, name ≠ .j3 ∧ Nonempty (G ≃* name.Carrier)) ∨
    Nonempty (G ≃* Janko1.Model)

/-- All five source alternatives of Theorem B; B(3) is split into its
rank-one and rank-two families, and B(4) into linear and symplectic families. -/
inductive IsTheoremBModel (G : Type u) [Group G] : Prop
  | alternating (n : ℕ) (hn : n ≤ 9) (iso : Nonempty (G ≃* alternatingGroup (Fin n)))
  | odd (model : IsTheoremBOddModel G)
  | bender (model : IsBenderModel G)
  | rank_two (f : ℕ) (model : IsRankTwoModel G f)
  | linear_binary (n : ℕ) (hn : n = 4 ∨ n = 5) (iso : ClassicalGroup.IsPSL G n 2)
  | symplectic_binary (iso : ClassicalGroup.IsPSp G 3 2)
  | sporadic (model : IsTheoremBSporadicModel G)

/-- All five source alternatives of Theorem C, with its stricter parameters. -/
inductive IsTheoremCModel (G : Type u) [Group G] : Prop
  | alternating (n : ℕ) (hn : n ≤ 8) (iso : Nonempty (G ≃* alternatingGroup (Fin n)))
  | odd (model : IsTheoremCOddModel G)
  | bender (model : IsBenderModel G)
  | rank_two (f : ℕ) (model : IsTheoremCRankTwoModel G f)
  | linear_binary (n : ℕ) (hn : n = 4 ∨ n = 5) (iso : ClassicalGroup.IsPSL G n 2)
  | sporadic (model : IsTheoremCSporadicModel G)

variable {G : Type u} {H : Type v} [Group G] [Group H]

theorem IsSpecialUnitaryModel.of_mulEquiv {n q : ℕ}
    (h : IsSpecialUnitaryModel G n q) (e : H ≃* G) : IsSpecialUnitaryModel H n q := by
  obtain ⟨F, hF, hfin, J, hcard, hconj, iso⟩ := h
  exact ⟨F, hF, hfin, J, hcard, hconj, iso.map fun a => e.trans a⟩

theorem IsTheoremBOddModel.of_mulEquiv (h : IsTheoremBOddModel G) (a : H ≃* G) :
    IsTheoremBOddModel H := by
  cases h with
  | linear_two q hq iso => exact .linear_two q hq (iso.of_mulEquiv a)
  | linear_three p e hp ho he iso => exact .linear_three p e hp ho he (iso.of_mulEquiv a)
  | unitary_three p e hp ho he iso => exact .unitary_three p e hp ho he (iso.of_mulEquiv a)
  | symplectic p hp ho iso => exact .symplectic p hp ho (iso.of_mulEquiv a)
  | g2 p hp ho iso => exact .g2 p hp ho (iso.of_mulEquiv a)
  | linear_four r hp hf iso => exact .linear_four r hp hf (iso.of_mulEquiv a)
  | unitary_four s hp hm iso => exact .unitary_four s hp hm (iso.of_mulEquiv a)

theorem IsTheoremCOddModel.of_mulEquiv (h : IsTheoremCOddModel G) (a : H ≃* G) :
    IsTheoremCOddModel H := by
  cases h with
  | linear_two p e hp ho he iso => exact .linear_two p e hp ho he (iso.of_mulEquiv a)
  | linear_three p hp ho iso => exact .linear_three p hp ho (iso.of_mulEquiv a)
  | unitary_three p hp ho iso => exact .unitary_three p hp ho (iso.of_mulEquiv a)

theorem IsTheoremCOddModel.toTheoremBOddModel (h : IsTheoremCOddModel G) :
    IsTheoremBOddModel G := by
  cases h with
  | linear_two p e _ ho _ iso => exact .linear_two (p ^ e) ho.pow iso
  | linear_three p hp ho iso =>
      exact .linear_three p 1 hp ho (by decide) (by simpa only [pow_one] using iso)
  | unitary_three p hp ho iso =>
      exact .unitary_three p 1 hp ho (by decide) (by simpa only [pow_one] using iso)

/-- The displayed source presentation `r = 2^a + 1` gives the Fermat branch:
primality forces the positive exponent to be a power of two. -/
theorem IsTheoremBOddModel.linear_four_of_two_power {r : ℕ}
    (hp : r.Prime) (ho : Odd r) (hf : ∃ a : ℕ, r = 2 ^ a + 1)
    (iso : ClassicalGroup.IsPSL G 4 r) : IsTheoremBOddModel G := by
  obtain ⟨a, rfl⟩ := hf
  have ha : a ≠ 0 := by
    rintro rfl
    exact (by decide : ¬ Odd (2 ^ 0 + 1 : ℕ)) ho
  obtain ⟨k, rfl⟩ := Nat.pow_of_pow_add_prime (by decide : 1 < 2) ha hp
  exact .linear_four _ hp ⟨k, rfl⟩ iso

/-- The subtraction notation `s = 2^b - 1` in B(2) agrees with the
successor notation in its actual unitary model alternative. -/
theorem IsTheoremBOddModel.unitary_four_of_mersenne {s : ℕ}
    (hp : s.Prime) (hm : ∃ b : ℕ, s = 2 ^ b - 1)
    (iso : ClassicalGroup.IsPSU G 4 s) : IsTheoremBOddModel G := by
  obtain ⟨b, hb⟩ := hm
  have hpow : 1 ≤ 2 ^ b := Nat.one_le_pow b 2 (by decide)
  exact .unitary_four s hp ⟨b, by omega⟩ iso

theorem IsTheoremCRankTwoModel.toRankTwoModel {f : ℕ}
    (h : IsTheoremCRankTwoModel G f) : IsRankTwoModel G f := by
  cases h with
  | linear hf iso => exact .linear hf iso
  | symplectic hf iso => exact .symplectic hf iso
  | g2 hf iso => exact .g2 hf iso
  | triality hf iso => exact .triality hf iso
  | ree_f4 m hm hf iso => exact .ree_f4 m hm hf iso
  | symplectic_derived hf iso => exact .symplectic_derived hf iso
  | g2_derived hf iso => exact .g2_derived hf iso
  | tits hf iso => exact .tits hf iso

theorem IsTheoremCRankTwoModel.of_mulEquiv {f : ℕ}
    (h : IsTheoremCRankTwoModel G f) (e : H ≃* G) : IsTheoremCRankTwoModel H f := by
  cases h with
  | linear hf iso => exact .linear hf (iso.of_mulEquiv e)
  | symplectic hf iso => exact .symplectic hf (iso.of_mulEquiv e)
  | g2 hf iso => exact .g2 hf (iso.of_mulEquiv e)
  | triality hf iso => exact .triality hf (iso.of_mulEquiv e)
  | ree_f4 m hm hf iso => exact .ree_f4 m hm hf (iso.map fun a => e.trans a)
  | symplectic_derived hf iso => exact .symplectic_derived hf (iso.map fun a => e.trans a)
  | g2_derived hf iso => exact .g2_derived hf (iso.map fun a => e.trans a)
  | tits hf iso => exact .tits hf (iso.map fun a => e.trans a)

theorem IsTheoremBSporadicModel.of_mulEquiv (h : IsTheoremBSporadicModel G) (e : H ≃* G) :
    IsTheoremBSporadicModel H :=
  h.imp (fun h => h.of_mulEquiv e)
    (fun h => h.imp (fun iso => iso.map fun a => e.trans a) (fun iso => iso.map fun a => e.trans a))

theorem IsTheoremCSporadicModel.of_mulEquiv (h : IsTheoremCSporadicModel G) (e : H ≃* G) :
    IsTheoremCSporadicModel H := by
  rcases h with ⟨name, hn, iso⟩ | iso
  · exact .inl ⟨name, hn, iso.map fun a => e.trans a⟩
  · exact .inr (iso.map fun a => e.trans a)

theorem IsTheoremCSporadicModel.toTheoremBSporadicModel (h : IsTheoremCSporadicModel G) :
    IsTheoremBSporadicModel G := by
  rcases h with ⟨name, _, iso⟩ | iso
  · exact .inl ⟨name, iso⟩
  · exact .inr (.inl iso)

theorem IsTheoremCModel.toTheoremBModel (h : IsTheoremCModel G) : IsTheoremBModel G := by
  cases h with
  | alternating n hn iso => exact .alternating n (by omega) iso
  | odd h => exact .odd h.toTheoremBOddModel
  | bender h => exact .bender h
  | rank_two f h => exact .rank_two f h.toRankTwoModel
  | linear_binary n hn iso => exact .linear_binary n hn iso
  | sporadic h => exact .sporadic h.toTheoremBSporadicModel

theorem IsTheoremBModel.of_mulEquiv (h : IsTheoremBModel G) (e : H ≃* G) :
    IsTheoremBModel H := by
  cases h with
  | alternating n hn iso => exact .alternating n hn (iso.map fun a => e.trans a)
  | odd h => exact .odd (h.of_mulEquiv e)
  | bender h => exact .bender (h.of_mulEquiv e)
  | rank_two f h => exact .rank_two f (h.of_mulEquiv e)
  | linear_binary n hn iso => exact .linear_binary n hn (iso.of_mulEquiv e)
  | symplectic_binary iso => exact .symplectic_binary (iso.of_mulEquiv e)
  | sporadic h => exact .sporadic (h.of_mulEquiv e)

theorem IsTheoremCModel.of_mulEquiv (h : IsTheoremCModel G) (e : H ≃* G) :
    IsTheoremCModel H := by
  cases h with
  | alternating n hn iso => exact .alternating n hn (iso.map fun a => e.trans a)
  | odd h => exact .odd (h.of_mulEquiv e)
  | bender h => exact .bender (h.of_mulEquiv e)
  | rank_two f h => exact .rank_two f (h.of_mulEquiv e)
  | linear_binary n hn iso => exact .linear_binary n hn (iso.of_mulEquiv e)
  | sporadic h => exact .sporadic (h.of_mulEquiv e)

theorem isTheoremBModel_mulEquiv_iff (e : G ≃* H) : IsTheoremBModel G ↔ IsTheoremBModel H :=
  ⟨fun h => h.of_mulEquiv e.symm, fun h => h.of_mulEquiv e⟩

theorem isTheoremCModel_mulEquiv_iff (e : G ≃* H) : IsTheoremCModel G ↔ IsTheoremCModel H :=
  ⟨fun h => h.of_mulEquiv e.symm, fun h => h.of_mulEquiv e⟩

end CFSG.Quasithin.ChapterA.Section02
