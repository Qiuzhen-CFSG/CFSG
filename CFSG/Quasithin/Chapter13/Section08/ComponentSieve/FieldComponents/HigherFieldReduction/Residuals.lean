module

public import CFSG.Quasithin.Chapter13.Section08.SourceDefs
public import Theory.GroupTheory.PResidual.PerfectCover

/-!
# Borel lifts and residuals in the higher-field reduction

The source is the proof of Aschbacher–Smith 13.8.20, printed pp.954–955
(combined manuscript, 1 March 2004). The Borel is lifted inside K through the
restriction of H → H/O₂(H). Its two-residual therefore has exactly the
required residual image in H*, without identifying K* with K/O₂(K).

The centralizer of L/O₂(L) is expressed by commutators modulo the embedded
O₂(L); normality is required only in the relevant local overgroup. Both B
and B_C are two-residuals, and the torus calculation uses the three-residual
of B. These definitions do not assert existence or structure of a model Borel.

The action kernel C_T(K) is contained in the torus centralizer. Thus a
calculation in Aut(K) must retain this kernel when lifted to T. The source
trichotomy and the outer-automorphism commutator orders remain to be proved.
-/

@[expose] public section

open Subgroup
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction
variable {G : Type*} [Group G]

/-- A residual of a subgroup, embedded in the ambient group. -/
abbrev residualIn (p : ℕ) (D : Subgroup G) : Subgroup G :=
  (pResidual p D).map D.subtype

/-- Restrict H → H/O₂(H) to a specified subgroup K ≤ H. -/
def starHom (H K : Subgroup G) (hKH : K ≤ H) : K →* Source.Hstar H :=
  (QuotientGroup.mk' (pCore 2 H)).comp (inclusion hKH)

/-- Passing from a subgroup of K to its ambient image respects the actual star map. -/
theorem starImage_map_subtype (H K : Subgroup G) (hKH : K ≤ H) (D : Subgroup K) :
    Source.starImage H (D.map K.subtype) = D.map (starHom H K hKH) := by
  have h : (D.map K.subtype).subgroupOf H = D.map (inclusion hKH) := by
    ext x
    constructor
    · rintro ⟨y, hy, he⟩
      exact ⟨y, hy, Subtype.ext he⟩
    · rintro ⟨y, hy, he⟩
      exact ⟨y, hy, congrArg Subtype.val he⟩
  rw [Source.starImage, h, map_map]
  rfl

/-- The restricted quotient homomorphism has image K*. -/
theorem range_starHom (H K : Subgroup G) (hKH : K ≤ H) :
    (starHom H K hKH).range = Source.starImage H K := by
  have h := starImage_map_subtype H K hKH (⊤ : Subgroup K)
  simpa only [← MonoidHom.range_eq_map, range_subtype] using h.symm

/-- The inverse image is taken inside K, rather than inside all of H. -/
def borelLift (H K : Subgroup G) (hKH : K ≤ H)
    (B₀star : Subgroup (Source.Hstar H)) : Subgroup G :=
  (B₀star.comap (starHom H K hKH)).map K.subtype

/-- The lift stays inside K. -/
theorem borelLift_le (H K : Subgroup G) (hKH : K ≤ H)
    (B₀star : Subgroup (Source.Hstar H)) : borelLift H K hKH B₀star ≤ K :=
  map_subtype_le _

/-- A Borel of K* is the image of its lift inside K. -/
theorem starImage_borelLift (H K : Subgroup G) (hKH : K ≤ H)
    (B₀star : Subgroup (Source.Hstar H)) (hB : B₀star ≤ Source.starImage H K) :
    Source.starImage H (borelLift H K hKH B₀star) = B₀star := by
  rw [borelLift, starImage_map_subtype H K hKH]
  exact map_comap_eq_self (by simpa only [range_starHom] using hB)

/-- A finite residual maps to the residual of the actual star image. -/
theorem starImage_residualIn [Finite G] (p : ℕ) (H D : Subgroup G) (hDH : D ≤ H) :
    Source.starImage H (residualIn p D) = residualIn p (Source.starImage H D) := by
  rw [starImage_map_subtype H D hDH]
  have h := map_pResidual_of_surjective p (starHom H D hDH).rangeRestrict
    (starHom H D hDH).rangeRestrict_surjective
  have hm := congrArg (fun S => S.map (starHom H D hDH).range.subtype) h
  rw [map_map] at hm
  change (pResidual p D).map (starHom H D hDH) = _ at hm
  rw [range_starHom H D hDH] at hm
  exact hm

/-- The source B is the two-residual of the lifted Borel. -/
def borelResidual (B₀ : Subgroup G) : Subgroup G := residualIn 2 B₀

/-- Lifting the Borel inside K and taking its residual commutes with passing to H*. -/
theorem starImage_borelResidual [Finite G] (H K : Subgroup G) (hKH : K ≤ H)
    (B₀star : Subgroup (Source.Hstar H)) (hB : B₀star ≤ Source.starImage H K) :
    Source.starImage H (borelResidual (borelLift H K hKH B₀star)) =
      residualIn 2 B₀star := by
  rw [borelResidual, starImage_residualIn 2 H _ ((borelLift_le H K hKH B₀star).trans hKH),
    starImage_borelLift H K hKH B₀star hB]

/-- The source centralizer is the centralizer of L/O₂(L) inside BL₁. -/
def borelCentralizer (B L₁ L : Subgroup G) : Subgroup G :=
  commutatorPreimage (B ⊔ L₁) L (L.pCoreIn 2)

/-- The source B_C is a two-residual, not a two-core. -/
def centralizingResidual (B L₁ L : Subgroup G) : Subgroup G :=
  residualIn 2 (borelCentralizer B L₁ L)

/-- Every element of B_C centralizes L modulo O₂(L). -/
theorem centralizingResidual_commutator_le (B L₁ L : Subgroup G)
    (hN : B ⊔ L₁ ≤ normalizer (L.pCoreIn 2)) :
    ⁅centralizingResidual B L₁ L, L⁆ ≤ L.pCoreIn 2 :=
  (commutator_mono (map_subtype_le _) le_rfl).trans
    (commutator_commutatorPreimage_le _ _ _ hN)

/-- A finite p-prime subgroup is its own p-residual. -/
private theorem residualIn_eq_self_of_coprime [Finite G] (p : ℕ) (B : Subgroup G)
    (hB : Nat.Coprime p (Nat.card B)) : residualIn p B = B := by
  apply le_antisymm (map_subtype_le _)
  intro b hb
  exact mem_map.mpr ⟨⟨b, hb⟩,
    mem_pResidual_of_orderOf_coprime (hB.of_dvd_right (orderOf_dvd_natCard (x := (⟨b, hb⟩ : B)))), rfl⟩

/-- The torus centralizer is expressed by commutators modulo O₂(B). -/
def torusCentralizer (T B : Subgroup G) : Subgroup G :=
  commutatorPreimage T (residualIn 3 B ⊔ B.pCoreIn 2) (B.pCoreIn 2)

/-- The kernel of the action on K must be retained in the torus centralizer. -/
theorem central_kernel_le_torusCentralizer (T B K : Subgroup G) (hBK : B ≤ K) :
    T ⊓ centralizer (K : Set G) ≤ torusCentralizer T B := by
  apply le_commutatorPreimage inf_le_left
  have hC : T ⊓ centralizer (K : Set G) ≤
      centralizer ((residualIn 3 B ⊔ B.pCoreIn 2 : Subgroup G) : Set G) := by
    apply inf_le_right.trans
    apply Subgroup.centralizer_le
    exact (sup_le (map_subtype_le _) (pCoreIn_le 2 B)).trans hBK
  rw [commutator_eq_bot_iff_le_centralizer.mpr hC]
  exact bot_le

/-- The odd-degree linear branch needs only the three-prime order of B and
containment of its three-residual in B_C to make B centralize V. -/
theorem borel_centralizes_of_threePrime [Finite G] (B C V : Subgroup G)
    (hcard : Nat.Coprime 3 (Nat.card B)) (hR : residualIn 3 B ≤ C)
    (hC : C ≤ centralizer (V : Set G)) : B ≤ centralizer (V : Set G) := by
  rw [← residualIn_eq_self_of_coprime 3 B hcard]
  exact hR.trans hC

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction

end
