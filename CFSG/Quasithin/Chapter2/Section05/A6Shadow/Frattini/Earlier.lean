module

public import CFSG.Quasithin.Chapter2.Defs
public import CFSG.Quasithin.Chapter1.Defs
public import CFSG.Quasithin.Defs
public import Theory.SpecificGroups.AlternatingSix.ShadowLocal.Transport
public import Theory.GroupTheory.DisjointConjugateCenter

/-!
# Earlier inputs for the A₆ Frattini argument

Source: Aschbacher–Smith, combined 1 March 2004 manuscript, Notation 2.5.4,
2.5.5, 2.5.8, 2.5.9, 2.5.11–13, and the A₆ reduction preceding 2.5.22,
printed pp.554–558 and 567. The section assembly constructs this interface.
Each field records an earlier source clause. No assertion of 2.5.22(1),
2.5.23–27, or a maximal elementary subgroup classification is an input.

Subgroups live in G; normality is relative to H. Right conjugation is
`x⁻¹ a x`, whereas the homomorphism to Aut(A₆) uses `MulAut.conj`, hence
left conjugation. The conversion is explicit in `rightConjugate`.
The two starred local families are not identified.
-/

@[expose] public section

open Subgroup
namespace CFSG.Quasithin.Chapter2.A6Shadow.Frattini

universe u

/-- Right conjugation of subgroups, with the inverse required by `MulAut.conj`. -/
def rightConjugate {G : Type*} [Group G] (x : G) (A : Subgroup G) : Subgroup G :=
  A.map (MulAut.conj x⁻¹).toMonoidHom

/-- The common earlier-source data. In particular `properK` is retained in
`simpleQTKE`; the actual A₆ model and compatible action are part of the data. -/
structure EarlierSetup (κ : GroupClass.{u}) (G : Type u) [Group G] [Finite G] where
  /-- The section's simple QTKE hypothesis, including proper-K. -/
  simpleQTKE : IsSimpleQTKE κ G
  H : Subgroup G
  K : Subgroup G
  S : Subgroup G
  M : Subgroup G
  T : Sylow 2 G
  /-- The unique maximal two-local over T, the standing Chapter 2 hypothesis. -/
  maximalM : IsMaximalTwoLocal M
  t_le_m : (T : Subgroup G) ≤ M
  unique_maximal : ∀ L : Subgroup G, IsMaximalTwoLocal L → (T : Subgroup G) ≤ L → L = M
  /-- The superscript-star choice of Notation 2.5.9. -/
  star : H ∈ gammaStar (Chapter1.He G) M
  /-- The standing hypothesis of §2.5. -/
  even_empty : gammaEvenZero (Chapter1.He G) M = ∅
  /-- K = K₀ and H = KS, Notation 2.5.4 and the reduction preceding 2.5.22. -/
  generated : H = K ⊔ S
  normalK : (K.subgroupOf H).Normal
  modelK : K ≃* alternatingGroup (Fin 6)
  /-- Source 2.5.2(2): the Borel intersection in the A₆ branch is its Sylow two-subgroup. -/
  intersection_m : K ⊓ M = S ⊓ K
  sylow : Sylow 2 H
  sylow_eq : (sylow : Subgroup H).map H.subtype = S
  s_le_t : S ≤ (T : Subgroup G)
  SC : Subgroup G
  /-- Notation 2.5.4: S_C = C_S(K) = O₂(H). -/
  centralizer_K : SC = S ⊓ centralizer (K : Set G)
  core : SC = twoCore H
  x : G
  /-- The crossing element of Notation 2.5.4. -/
  x_mem : x ∈ T
  x_normalizes : x ∈ normalizer (S : Set G)
  x_outside : x ∉ S
  square_mem : x ^ 2 ∈ S
  /-- Source 2.5.5(1). -/
  disjoint_conjugate : Disjoint SC (rightConjugate x SC)
  /-- Source 2.5.5(2). -/
  commuting_conjugate : SC ≤ centralizer (rightConjugate x SC : Set G)
  t : G
  z : G
  zK : G
  /-- The distinguished involutions of 2.5.8(4) and 2.5.11(1). -/
  t_mem : t ∈ SC
  t_order : orderOf t = 2
  z_order : orderOf z = 2
  zK_order : orderOf zK = 2
  center_t : centerIn (T : Subgroup G) = zpowers z
  center_s : centerIn S = zpowers t ⊔ zpowers zK
  center_sc : centerIn S ⊓ SC = zpowers t
  center_sk : centerIn (S ⊓ K) = zpowers zK
  /-- Source 2.5.11(2). -/
  h_le_centralizer_t : H ≤ centralizer ({t} : Set G)
  /-- Source 2.5.20 with K = K₀: relative normality in G_t. -/
  centralizer_t_normalizes_K : centralizer ({t} : Set G) ≤ normalizer (K : Set G)
  sylow_centralizer_t : ∃ P : Sylow 2 (centralizer ({t} : Set G)),
    (P : Subgroup (centralizer ({t} : Set G))).map
      (centralizer ({t} : Set G)).subtype = S
  t_not_conjugate_z : ∀ g : G, g⁻¹ * z * g ≠ t
  /-- Source 2.5.13(1); it does not choose between the two possibilities for z. -/
  crossing_t : x⁻¹ * t * x = t * z
  /-- The actual quotient action from the reduction to H̄ = Aut(A₆). -/
  action : H →* MulAut (alternatingGroup (Fin 6))
  action_surjective : Function.Surjective action
  action_compatible : ∀ (h : H) (k : K),
    (modelK.symm (action h (modelK k)) : G) = (h : G) * k * (h : G)⁻¹
  action_kernel : action.ker = SC.subgroupOf H

/-- The literal family U*(H): maximal first-coordinate order in the global U.
This does not impose the extra condition U ≤ S of source 2.5.12(3). -/
def largestLocalPairs {G : Type*} [Group G] (M H : Subgroup G) :
    Set (Subgroup G × Subgroup G) :=
  {P | P ∈ localPairsIn (Chapter1.He G) M H ∧
    ∀ W ∈ localBases (Chapter1.He G) M, Nat.card W ≤ Nat.card P.1}

end CFSG.Quasithin.Chapter2.A6Shadow.Frattini
