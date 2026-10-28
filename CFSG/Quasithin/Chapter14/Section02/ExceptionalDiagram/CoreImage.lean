module
public import CFSG.Quasithin.Chapter12.Section08.Parabolic.Basic
public import Theory.SpecificGroups.PSL3Four.NormalElementarySylow
public import Theory.GroupTheory.LocalNormalizerUniqueness

/-!
# The elementary core image in the exceptional diagram branch

In the nonabelian paragraph of 14.2.13, the preceding parabolic source
gives O₂(I₂) = W Xᵍ. An action killing U kills W. Squares of Xᵍ lie in
V ≤ U, since g normalizes V; its image, and hence the whole core image,
is elementary abelian. Relative normality of I₂ in G₂ makes the core
T-invariant. The literal action image therefore satisfies the proved
PSL₃(4) placement theorem when the original Sylow acts on the diagram.

The core factorization, square bound and relative normality are the
preceding-source inputs from 12.8.4 and 12.8.9. No identification of U
with a span under another overgroup is required.

Source: Aschbacher--Smith, combined manuscript of 1 March 2004,
Lemma 14.2.13, printed p.984, and Lemmas 12.8.4, 12.8.9.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative

namespace CFSG.Quasithin.Chapter14.Section02.ExceptionalDiagram
open Chapter12.Section08
variable {G A : Type*} [Group G] [Group A]
variable {T : Sylow 2 G} {V : Subgroup G}

/-- Killing the original span leaves precisely the displaced factor image. -/
theorem core_image_eq_displaced (F : InvariantFlag T V 2) [IsMulCommutative V]
    (L : Subgroup G) (hL : L ≤ normalizer (V : Set G))
    (g : G) (hg : g ∈ F.P L)
    (hsplit : (F.I₂ L).pCoreIn 2 = F.W ⊔ F.X g)
    (ρ : F.H →* A) (hkill : F.U.subgroupOf F.H ≤ ρ.ker) :
    (((F.I₂ L).pCoreIn 2).subgroupOf F.H).map ρ =
      ((F.X g).subgroupOf F.H).map ρ := by
  have hWH : F.W ≤ F.H := inf_le_left.trans F.U_le_H
  have hXH : F.X g ≤ F.H := F.X_le_H g (F.P_le_G₂ (by omega) L hL hg)
  have hWkill : F.W.subgroupOf F.H ≤ ρ.ker := by
    intro w hw
    exact hkill (show (w : G) ∈ F.U from hw.1)
  rw [hsplit, subgroupOf_sup hWH hXH, Subgroup.map_sup,
    (Subgroup.map_eq_bot_iff _).mpr hWkill, bot_sup_eq]

/-- The actual core has elementary image under every action killing U. -/
theorem core_image_elementary (F : InvariantFlag T V 2) [IsMulCommutative V]
    (L : Subgroup G) (hL : L ≤ normalizer (V : Set G))
    (g : G) (hg : g ∈ F.P L)
    (hsplit : (F.I₂ L).pCoreIn 2 = F.W ⊔ F.X g)
    (hsquare : ∀ u ∈ F.U, u ^ 2 ∈ F.Vi 1)
    (ρ : F.H →* A) (hkill : F.U.subgroupOf F.H ≤ ρ.ker) :
    IsElementaryAbelian 2 ((((F.I₂ L).pCoreIn 2).subgroupOf F.H).map ρ) := by
  rw [core_image_eq_displaced F L hL g hg hsplit ρ hkill]
  have hsq : ∀ a : ((F.X g).subgroupOf F.H).map ρ, a ^ 2 = 1 := by
    intro a
    apply Subtype.ext
    obtain ⟨x,hx,heq⟩ := a.property
    change (a : A) ^ 2 = 1
    rw [← heq]
    have hx2 : (x : G) ^ 2 ∈ V := by
      obtain ⟨w,hw,he⟩ := hx
      have hconj : (x : G) ^ 2 ∈ conjugate (F.Vi 1) g := by
        have hh := mem_map_of_mem (MulAut.conj g⁻¹).toMonoidHom
          (hsquare w hw.1)
        change (MulAut.conj g⁻¹) (w ^ 2) ∈ conjugate (F.Vi 1) g at hh
        rw [map_pow] at hh
        have he' : (MulAut.conj g⁻¹) w = (x : G) := he
        rwa [he'] at hh
      exact conjugate_le_of_normalizes (F.le_seed 1) g
        (F.P_le_seed_normalizer L hL hg) hconj
    have hk : x ^ 2 ∈ ρ.ker := hkill
      (show ((x ^ 2 : F.H) : G) ∈ F.U from (le_conjugateSpanBy V F.H) hx2)
    exact (map_pow ρ x 2).symm.trans hk
  refine { toIsMulCommutative := ?_, exponent_dvd_p := ?_ }
  · exact ⟨⟨fun a b => (Commute.of_orderOf_dvd_two
      (fun x => orderOf_dvd_of_pow_eq_one (hsq x)) a b).eq⟩⟩
  · exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr hsq

/-- The core is T-invariant by relative normality of the original I₂. -/
theorem core_normalized_by_sylow (F : InvariantFlag T V 2) (L : Subgroup G)
    (hIG : F.I₂ L ≤ F.Gi 2)
    [((F.I₂ L).subgroupOf (F.Gi 2)).Normal] :
    (T : Subgroup G) ≤ normalizer (((F.I₂ L).pCoreIn 2 : Subgroup G) : Set G) := by
  have hNI : F.Gi 2 ≤ normalizer (F.I₂ L : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hIG).mp inferInstance
  exact (F.invariant 2).trans (hNI.trans
    (normalizer_le_normalizer_characteristic_image (F.I₂ L) (pCore 2 (F.I₂ L))))

/-- All literal image inputs required by the exceptional model placement. -/
theorem core_image_geometry (F : InvariantFlag T V 2) [IsMulCommutative V]
    (L : Subgroup G) (hL : L ≤ normalizer (V : Set G))
    (g : G) (hg : g ∈ F.P L)
    (hsplit : (F.I₂ L).pCoreIn 2 = F.W ⊔ F.X g)
    (hsquare : ∀ u ∈ F.U, u ^ 2 ∈ F.Vi 1)
    (hIG : F.I₂ L ≤ F.Gi 2)
    [((F.I₂ L).subgroupOf (F.Gi 2)).Normal]
    (hQT : (F.I₂ L).pCoreIn 2 ≤ (T : Subgroup G))
    (ρ : F.H →* A) (hkill : F.U.subgroupOf F.H ≤ ρ.ker) :
    let S : Sylow 2 F.H := T.subtype (F.invariant 1)
    let E := (((F.I₂ L).pCoreIn 2).subgroupOf F.H).map ρ
    IsElementaryAbelian 2 E ∧ E ≤ (S : Subgroup F.H).map ρ ∧
      (S : Subgroup F.H).map ρ ≤ normalizer (E : Set A) := by
  let S : Sylow 2 F.H := T.subtype (F.invariant 1)
  let Q := ((F.I₂ L).pCoreIn 2).subgroupOf F.H
  have hQS : Q ≤ (S : Subgroup F.H) := by
    intro q hq
    exact hQT hq
  have hn : (S : Subgroup F.H) ≤ normalizer (Q : Set F.H) := by
    apply le_normalizer_iff.mpr
    intro t ht q hq
    exact le_normalizer_iff.mp (core_normalized_by_sylow F L hIG)
      (t : G) ht (q : G) hq
  exact ⟨core_image_elementary F L hL g hg hsplit hsquare ρ hkill,
    map_mono hQS, (map_mono hn).trans (Q.le_normalizer_map ρ)⟩

/-- The nonabelian source13 calculation applied to the actual quotient action. -/
theorem core_image_le_inner [Finite G]
    (F : InvariantFlag T V 2) [IsMulCommutative V]
    (L : Subgroup G) (hL : L ≤ normalizer (V : Set G))
    (g : G) (hg : g ∈ F.P L)
    (hsplit : (F.I₂ L).pCoreIn 2 = F.W ⊔ F.X g)
    (hsquare : ∀ u ∈ F.U, u ^ 2 ∈ F.Vi 1)
    (hIG : F.I₂ L ≤ F.Gi 2)
    [((F.I₂ L).subgroupOf (F.Gi 2)).Normal]
    (hQT : (F.I₂ L).pCoreIn 2 ≤ (T : Subgroup G))
    (ρ : F.H →* MulAut Matrix.PSL3Four.PSL)
    (hkill : F.U.subgroupOf F.H ≤ ρ.ker)
    (hinner : MulAut.innerSubgroup Matrix.PSL3Four.PSL ≤ ρ.range)
    (hswap : ∃ t ∈ ((T.subtype (show (T : Subgroup G) ≤ F.H from F.invariant 1) :
        Sylow 2 F.H) : Subgroup F.H),
      Matrix.PSL3.LinearThree.OuterExtensions.diagramAction Matrix.PSL3Four.F
        (n := 2) (by decide) (by simpa using Matrix.PSL3Four.card_F) (ρ t) ≠ 1) :
    (((F.I₂ L).pCoreIn 2).subgroupOf F.H).map ρ ≤
      MulAut.innerSubgroup Matrix.PSL3Four.PSL := by
  obtain ⟨he,hES,hn⟩ := core_image_geometry F L hL g hg hsplit hsquare hIG hQT ρ hkill
  let := he
  exact Matrix.PSL3Four.NormalElementarySylow.normal_elementary_le_inner_of_sylow_image
    ρ hinner (T.subtype (F.invariant 1)) _ hES hn hswap

private theorem subgroupOf_image_inclusion (B H J : Subgroup G)
    (hBH : B ≤ H) (hHJ : H ≤ J) (ρ : J →* A) :
    (B.subgroupOf J).map ρ =
      (B.subgroupOf H).map (ρ.comp (H.inclusion hHJ)) := by
  ext a
  constructor
  · rintro ⟨x,hx,he⟩
    exact ⟨⟨(x : G),hBH hx⟩,hx,he⟩
  · rintro ⟨x,hx,he⟩
    exact ⟨⟨(x : G),hHJ x.property⟩,hx,he⟩

/-- The elementary image calculation for the original overgroup action,
without transporting that action through an equality of subgroups. -/
theorem core_image_elementary_in_overgroup
    (F : InvariantFlag T V 2) [IsMulCommutative V]
    (L : Subgroup G) (hL : L ≤ normalizer (V : Set G))
    (g : G) (hg : g ∈ F.P L)
    (hsplit : (F.I₂ L).pCoreIn 2 = F.W ⊔ F.X g)
    (hsquare : ∀ u ∈ F.U, u ^ 2 ∈ F.Vi 1)
    (J : Subgroup G) (hHJ : F.H ≤ J)
    (ρ : J →* A) (hkill : F.U.subgroupOf J ≤ ρ.ker) :
    IsElementaryAbelian 2 ((((F.I₂ L).pCoreIn 2).subgroupOf J).map ρ) := by
  have hQH : (F.I₂ L).pCoreIn 2 ≤ F.H := by
    rw [hsplit]
    exact sup_le (inf_le_left.trans F.U_le_H)
      (F.X_le_H g (F.P_le_G₂ (by omega) L hL hg))
  rw [subgroupOf_image_inclusion _ _ _ hQH hHJ ρ]
  apply core_image_elementary F L hL g hg hsplit hsquare
  intro u hu
  exact hkill (show (⟨(u : G),hHJ u.property⟩ : J) ∈ F.U.subgroupOf J from hu)

/-- The literal overgroup core image is normal in the actual Sylow image. -/
theorem core_image_geometry_in_overgroup
    (F : InvariantFlag T V 2) [IsMulCommutative V]
    (L : Subgroup G) (hL : L ≤ normalizer (V : Set G))
    (g : G) (hg : g ∈ F.P L)
    (hsplit : (F.I₂ L).pCoreIn 2 = F.W ⊔ F.X g)
    (hsquare : ∀ u ∈ F.U, u ^ 2 ∈ F.Vi 1)
    (hQT : (F.I₂ L).pCoreIn 2 ≤ (T : Subgroup G))
    (hnorm : (T : Subgroup G) ≤
      normalizer ((F.I₂ L).pCoreIn 2 : Set G))
    (J : Subgroup G) (hHJ : F.H ≤ J)
    (ρ : J →* A) (hkill : F.U.subgroupOf J ≤ ρ.ker) :
    let S : Sylow 2 J := T.subtype ((F.invariant 1).trans hHJ)
    let E := (((F.I₂ L).pCoreIn 2).subgroupOf J).map ρ
    IsElementaryAbelian 2 E ∧ E ≤ (S : Subgroup J).map ρ ∧
      (S : Subgroup J).map ρ ≤ normalizer (E : Set A) := by
  let S : Sylow 2 J := T.subtype ((F.invariant 1).trans hHJ)
  let Q := ((F.I₂ L).pCoreIn 2).subgroupOf J
  have hQS : Q ≤ (S : Subgroup J) := by
    intro q hq
    exact hQT hq
  have hn : (S : Subgroup J) ≤ normalizer (Q : Set J) := by
    apply le_normalizer_iff.mpr
    intro t ht q hq
    exact le_normalizer_iff.mp hnorm (t : G) ht (q : G) hq
  exact ⟨core_image_elementary_in_overgroup F L hL g hg hsplit hsquare J hHJ ρ hkill,
    map_mono hQS, (map_mono hn).trans (Q.le_normalizer_map ρ)⟩

/-- The source13 core image for the original Mc action is inner. The square
and core data are precisely the original 12.8.4 and 12.8.9 outputs. -/
theorem core_image_le_inner_in_overgroup [Finite G]
    (F : InvariantFlag T V 2) [IsMulCommutative V]
    (L : Subgroup G) (hL : L ≤ normalizer (V : Set G))
    (g : G) (hg : g ∈ F.P L)
    (hsplit : (F.I₂ L).pCoreIn 2 = F.W ⊔ F.X g)
    (hsquare : ∀ u ∈ F.U, u ^ 2 ∈ F.Vi 1)
    (hQT : (F.I₂ L).pCoreIn 2 ≤ (T : Subgroup G))
    (hnorm : (T : Subgroup G) ≤
      normalizer ((F.I₂ L).pCoreIn 2 : Set G))
    (J : Subgroup G) (hHJ : F.H ≤ J)
    (ρ : J →* MulAut Matrix.PSL3Four.PSL)
    (hkill : F.U.subgroupOf J ≤ ρ.ker)
    (hinner : MulAut.innerSubgroup Matrix.PSL3Four.PSL ≤ ρ.range)
    (hswap : ∃ t ∈ ((T.subtype (show (T : Subgroup G) ≤ J from
        (F.invariant 1).trans hHJ) : Sylow 2 J) : Subgroup J),
      Matrix.PSL3.LinearThree.OuterExtensions.diagramAction Matrix.PSL3Four.F
        (n := 2) (by decide) (by simpa using Matrix.PSL3Four.card_F) (ρ t) ≠ 1) :
    (((F.I₂ L).pCoreIn 2).subgroupOf J).map ρ ≤
      MulAut.innerSubgroup Matrix.PSL3Four.PSL := by
  obtain ⟨he,hES,hn⟩ := core_image_geometry_in_overgroup F L hL g hg hsplit hsquare
    hQT hnorm J hHJ ρ hkill
  let := he
  exact Matrix.PSL3Four.NormalElementarySylow.normal_elementary_le_inner_of_sylow_image
    ρ hinner (T.subtype ((F.invariant 1).trans hHJ)) _ hES hn hswap

end CFSG.Quasithin.Chapter14.Section02.ExceptionalDiagram
