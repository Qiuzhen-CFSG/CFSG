module

public import CFSG.Quasithin.Chapter12.Section08.Parabolic.Basic
public import CFSG.Quasithin.Chapter12.Section08.Actions
public import Theory.GroupTheory.DisjointCommutingProduct
public import Theory.GroupTheory.PGroup.CharacteristicCenterReduction

/-!
# Centers of the marked binary parabolic

The first intersection follows by centralizing X and applying subgroup
modularity. The center of I₂ has trivial image in its S₃ quotient, and the
fixed-space calculation of 12.8.9(3) places it inside U; normalization by P
supplies the conjugate containment. These facts give the central involution
in the original Sylow T, the commutator containment, and the internal product.
The latter retains multiplication as its isomorphism. The final chain uses
the kernels of the literal Actions.uhatAction and localTildeAction maps.

`center_and_kernel_calculations_of_centralizer_center` consumes only the
stated preceding 12.8.3–9 consequences and the still-separate calculation
Z(W) = V₂ Z(U). It proves (1–3), the commutator part of (4), the internal
product part of (5), and all of (6). It is not the completed 12.8.10 theorem:
the centralizer identity, moved-rank bound, and minimal-parabolic induction
proving [L,Z(I₂)] = 1 must still be discharged by the Centers assembly owner.
The parent Parabolic owner discharges the preceding 12.8.9 inputs; the
Preliminary and Setup owners supply the earlier action and flag statements.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
Lemma 12.8.10, printed pp.853–854, PDF pp.870–871.
-/

open Subgroup
open scoped commutatorElement Pointwise
namespace CFSG.Quasithin.Chapter12.Section08
variable {G : Type*} [Group G]

private theorem centerIn_eq (A : Subgroup G) :
    centerIn A = A ⊓ centralizer (A : Set G) := by
  ext x
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨a.property, fun b hb => congrArg Subtype.val (mem_center_iff.mp ha ⟨b, hb⟩)⟩
  · rintro ⟨hx, hc⟩
    exact ⟨⟨x, hx⟩, mem_center_iff.mpr (fun a => Subtype.ext (hc a a.property)), rfl⟩

private theorem centerIn_le (A : Subgroup G) : centerIn A ≤ A := map_subtype_le _

private theorem centerIn_centralizes (A : Subgroup G) :
    centerIn A ≤ centralizer (A : Set G) := by rw [centerIn_eq]; exact inf_le_right

private theorem centers_le_center_join (A B : Subgroup G) :
    centerIn A ⊓ centerIn B ≤ centerIn (A ⊔ B) := by
  rw [centerIn_eq (A ⊔ B)]
  apply le_inf (inf_le_left.trans ((centerIn_le A).trans le_sup_left))
  apply le_centralizer_iff.mpr
  apply sup_le
  · exact le_centralizer_iff.mp (inf_le_left.trans (centerIn_centralizes A))
  · exact le_centralizer_iff.mp (inf_le_right.trans (centerIn_centralizes B))

private theorem inf_join_of_le (A B C : Subgroup G)
    (hBC : B ≤ C) (hBA : B ≤ normalizer (A : Set G)) :
    C ⊓ (A ⊔ B) = (C ⊓ A) ⊔ B := by
  apply le_antisymm _ (sup_le (le_inf inf_le_left (inf_le_right.trans le_sup_left))
    (le_inf hBC le_sup_right))
  rintro x ⟨hxC, hx⟩
  have hx' : x ∈ (A : Set G) * (B : Set G) := by
    rw [← coe_mul_of_right_le_normalizer_left A B hBA]
    exact hx
  obtain ⟨a, ha, b, hb, rfl⟩ := hx'
  have haC : a ∈ C := by
    have := C.mul_mem hxC (C.inv_mem (hBC hb))
    simpa using this
  exact mul_mem (mem_sup_left (show a ∈ C ⊓ A from ⟨haC, ha⟩)) (mem_sup_right hb)

private theorem normalizer_le_centerIn_normalizer (A : Subgroup G) :
    normalizer (A : Set G) ≤ normalizer (centerIn A : Set G) := by
  intro x hx
  apply (conjugate_eq_iff _ x).mp
  rw [← centerIn_conjugate, (conjugate_eq_iff A x).mpr hx]

private theorem conjugate_centralizer_eq (A : Subgroup G) (g : G)
    (hg : g ∈ normalizer (A : Set G)) :
    conjugate (centralizer (A : Set G)) g = centralizer (A : Set G) := by
  apply le_antisymm (conjugate_centralizer_le A g hg)
  calc
    centralizer (A : Set G) = conjugate (conjugate (centralizer (A : Set G)) g⁻¹) g :=
      (conjugate_conjugate_inv _ g).symm
    _ ≤ conjugate (centralizer (A : Set G)) g :=
      map_mono (conjugate_centralizer_le A g⁻¹ ((normalizer (A : Set G)).inv_mem hg))

namespace InvariantFlag
variable {T : Sylow 2 G} {V : Subgroup G} {n : ℕ}

public theorem plane_eq_point_join_conjugate (F : InvariantFlag T V n) [Finite G]
    [IsMulCommutative V] (hn : 2 ≤ n) (L : Subgroup G)
    (hL : L ≤ normalizer (V : Set G)) (g : G)
    (hgP : g ∈ F.P L) (hgH : g ∉ F.H) :
    F.Vi 2 = F.Vi 1 ⊔ conjugate (F.Vi 1) g := by
  have hgG := F.P_le_G₂ hn L hL hgP
  have hp : F.Vi 1 ≤ F.Vi 2 := F.monotone (by omega)
  have hpg : conjugate (F.Vi 1) g ≤ F.Vi 2 := conjugate_le_of_normalizes hp g hgG
  have hcard : Nat.card (F.Vi 1) = 2 := by simpa using F.card 1 (by omega)
  have hcardg : Nat.card (conjugate (F.Vi 1) g) = 2 := by
    rw [conjugate, card_map_of_injective (MulAut.conj g⁻¹).injective, hcard]
  have hd : Disjoint (F.Vi 1) (conjugate (F.Vi 1) g) := by
    apply disjoint_iff.mpr
    exact inf_eq_bot_of_card_two_of_ne _ _ hcard hcardg (fun he =>
      hgH ((conjugate_eq_iff (F.Vi 1) g).mp he.symm))
  have hc : F.Vi 1 ≤ centralizer (conjugate (F.Vi 1) g : Set G) := by
    intro x hx y hy
    exact congrArg Subtype.val (mul_comm' (⟨y, F.le_seed 2 (hpg hy)⟩ : V)
      ⟨x, F.le_seed 1 hx⟩)
  obtain ⟨e, _⟩ := exists_mulEquiv_prod_sup_of_disjoint_of_commuting _ _ hd hc
  have hj : Nat.card (F.Vi 1 ⊔ conjugate (F.Vi 1) g : Subgroup G) = 4 := by
    rw [← Nat.card_congr e.toEquiv, Nat.card_prod, hcard, hcardg]
  symm
  apply eq_of_le_of_card_ge (sup_le hp hpg)
  rw [hj, F.card 2 hn]
  decide

/-- Transporting the extraspecial centralizer calculation keeps the marked point. -/
public theorem conjugate_centralizer_center (F : InvariantFlag T V n) [Finite G]
    [IsMulCommutative V] (hn : 2 ≤ n) (L : Subgroup G)
    (hL : L ≤ normalizer (V : Set G))
    (hcenter : V ⊓ F.ZU = F.Vi 1)
    (hZW : centerIn F.W = F.Vi 2 ⊔ F.ZU)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H) :
    centerIn (F.X g) = conjugate F.ZU g ⊔ F.Vi 1 := by
  have hgG := F.P_le_G₂ hn L hL hgP
  have hp : F.Vi 1 ≤ F.ZU := by rw [← hcenter]; exact inf_le_right
  change centerIn (conjugate F.W g) = _
  rw [centerIn_conjugate, hZW, conjugate, Subgroup.map_sup]
  change conjugate (F.Vi 2) g ⊔ conjugate F.ZU g = _
  rw [(conjugate_eq_iff _ g).mpr hgG, F.plane_eq_point_join_conjugate hn L hL g hgP hgH,
    sup_assoc, sup_eq_right.mpr (show conjugate (F.Vi 1) g ≤ conjugate F.ZU g from map_mono hp), sup_comm]

/-- The first modular calculation, with its extraspecial centralizer input explicit. -/
private theorem center_intersection_of_centralizer (F : InvariantFlag T V n)
    (hn : 2 ≤ n) (L : Subgroup G) (hL : L ≤ normalizer (V : Set G))
    (hcenter : V ⊓ F.ZU = F.Vi 1)
    (hcomm : ⁅F.U, F.U⁆ ≤ F.Vi 1)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    (hZX : centerIn (F.X g) = conjugate F.ZU g ⊔ F.Vi 1) :
    F.ZU ⊓ conjugate F.U g = (F.ZU ⊓ conjugate F.ZU g) ⊔ F.Vi 1 := by
  have hgV := F.P_le_seed_normalizer L hL hgP
  have hgG := F.P_le_G₂ hn L hL hgP
  have hptZ : F.Vi 1 ≤ F.ZU := by rw [← hcenter]; exact inf_le_right
  have hptUg : F.Vi 1 ≤ conjugate F.U g := by
    calc
      F.Vi 1 ≤ V := F.le_seed 1
      _ = conjugate V g := ((conjugate_eq_iff V g).mpr hgV).symm
      _ ≤ conjugate F.U g := map_mono (le_conjugateSpanBy V F.H)
  have hZUUgX : F.ZU ⊓ conjugate F.U g ≤ F.X g := by
    intro x hx
    change x ∈ conjugate F.W g
    rw [W, conjugate_inf]
    refine ⟨hx.2, ?_⟩
    rw [conjugate_centralizer_eq _ g hgG]
    exact centralizer_le ((F.le_seed 2).trans (le_conjugateSpanBy V F.H))
      (centerIn_centralizes F.U hx.1)
  have hbound : ⁅F.ZU ⊓ conjugate F.U g, F.X g⁆ ≤ conjugate (F.Vi 1) g := by
    calc
      ⁅F.ZU ⊓ conjugate F.U g, F.X g⁆ ≤ ⁅conjugate F.U g, conjugate F.U g⁆ :=
        commutator_mono inf_le_right (map_mono inf_le_left)
      _ ≤ conjugate (F.Vi 1) g := by
        rw [conjugate, conjugate, ← map_commutator]
        exact map_mono hcomm
  have hboundZ : ⁅F.ZU ⊓ conjugate F.U g, F.X g⁆ ≤ F.ZU := by
    exact (commutator_mono inf_le_left le_rfl).trans
      (le_normalizer_iff_commutator_le_left.mp
        ((F.X_normalizes_U g hgG).trans (normalizer_le_centerIn_normalizer F.U)))
  have hc : ⁅F.ZU ⊓ conjugate F.U g, F.X g⁆ = ⊥ := by
    apply le_antisymm _ bot_le
    exact (le_inf hbound hboundZ).trans_eq (F.conjugate_point_inf_ZU (by omega) hcenter g hgV hgH)
  have hupper : F.ZU ⊓ conjugate F.U g ≤ centerIn (F.X g) := by
    rw [centerIn_eq]
    exact le_inf hZUUgX (commutator_eq_bot_iff_le_centralizer.mp hc)
  have hle : F.ZU ⊓ conjugate F.U g ≤ F.ZU ⊓ (conjugate F.ZU g ⊔ F.Vi 1) :=
    le_inf inf_le_left (hupper.trans_eq hZX)
  have hnorm : F.Vi 1 ≤ normalizer (conjugate F.ZU g : Set G) := by
    apply le_trans _ (centralizer_le_normalizer _)
    apply le_centralizer_iff.mpr
    rw [ZU, ← centerIn_conjugate]
    exact (centerIn_centralizes (conjugate F.U g)).trans (centralizer_le hptUg)
  rw [inf_join_of_le _ _ _ hptZ hnorm] at hle
  exact le_antisymm hle (sup_le
    (le_inf inf_le_left (inf_le_right.trans (map_mono (centerIn_le F.U))))
    (le_inf hptZ hptUg))

/-- The first clause, reduced only by the extraspecial centralizer calculation. -/
public theorem center_intersection (F : InvariantFlag T V n) [Finite G]
    [IsMulCommutative V] (hn : 2 ≤ n) (L : Subgroup G)
    (hL : L ≤ normalizer (V : Set G))
    (hcenter : V ⊓ F.ZU = F.Vi 1) (hcomm : ⁅F.U, F.U⁆ ≤ F.Vi 1)
    (hZW : centerIn F.W = F.Vi 2 ⊔ F.ZU)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H) :
    F.ZU ⊓ conjugate F.U g = (F.ZU ⊓ conjugate F.ZU g) ⊔ F.Vi 1 :=
  F.center_intersection_of_centralizer hn L hL hcenter hcomm g hgP hgH
    (F.conjugate_centralizer_center hn L hL hcenter hZW g hgP hgH)

/-- The symmetric formula uses the inverse of the same right conjugation. -/
public theorem conjugate_center_intersection (F : InvariantFlag T V n) [Finite G]
    [IsMulCommutative V] (hn : 2 ≤ n) (L : Subgroup G)
    (hL : L ≤ normalizer (V : Set G))
    (hcenter : V ⊓ F.ZU = F.Vi 1) (hcomm : ⁅F.U, F.U⁆ ≤ F.Vi 1)
    (hZW : centerIn F.W = F.Vi 2 ⊔ F.ZU)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H) :
    conjugate F.ZU g ⊓ F.U =
      (conjugate F.ZU g ⊓ F.ZU) ⊔ conjugate (F.Vi 1) g := by
  have he := F.center_intersection hn L hL hcenter hcomm hZW g⁻¹
    ((F.P L).inv_mem hgP) (fun hi => hgH (F.H.inv_mem_iff.mp hi))
  have he' := congrArg (fun A : Subgroup G => conjugate A g) he
  have hs (A B : Subgroup G) : conjugate (A ⊔ B) g = conjugate A g ⊔ conjugate B g :=
    Subgroup.map_sup _ _ _
  simpa only [conjugate_inf, hs, conjugate_conjugate_inv] using he'

/-- The commutator containment in 12.8.10(4), before passing to moved rank. -/
public theorem center_commutator_le_plane (F : InvariantFlag T V n) [Finite G]
    [IsMulCommutative V] (hn : 2 ≤ n) (L : Subgroup G)
    (hL : L ≤ normalizer (V : Set G))
    (hcenter : V ⊓ F.ZU = F.Vi 1) (hcomm : ⁅F.U, F.U⁆ ≤ F.Vi 1)
    (hZW : centerIn F.W = F.Vi 2 ⊔ F.ZU)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H) :
    ⁅F.W, conjugate F.ZU g⁆ ≤ F.ZU ⊔ F.Vi 2 := by
  have hgG := F.P_le_G₂ hn L hL hgP
  have hw : F.W ≤ normalizer (conjugate F.U g : Set G) := by
    have hi := F.X_normalizes_U g⁻¹ ((F.Gi 2).inv_mem hgG)
    have hm := (map_mono hi (f := (MulAut.conj g⁻¹).toMonoidHom)).trans
      (F.U.le_normalizer_map (MulAut.conj g⁻¹).toMonoidHom)
    change conjugate (conjugate F.W g⁻¹) g ≤ _ at hm
    rwa [conjugate_conjugate_inv] at hm
  have hwZ : F.W ≤ normalizer (conjugate F.ZU g : Set G) := by
    rw [ZU, ← centerIn_conjugate]
    exact hw.trans (normalizer_le_centerIn_normalizer _)
  have hZU : conjugate F.ZU g ≤ normalizer (F.U : Set G) :=
    (F.conjugate_ZU_le_X g).trans (F.X_normalizes_U g hgG)
  calc
    ⁅F.W, conjugate F.ZU g⁆ ≤ conjugate F.ZU g ⊓ F.U :=
      le_inf (le_normalizer_iff_commutator_le_right.mp hwZ)
        ((commutator_mono inf_le_left le_rfl).trans
          (le_normalizer_iff_commutator_le_left.mp hZU))
    _ = (conjugate F.ZU g ⊓ F.ZU) ⊔ conjugate (F.Vi 1) g :=
      F.conjugate_center_intersection hn L hL hcenter hcomm hZW g hgP hgH
    _ ≤ F.ZU ⊔ F.Vi 2 := sup_le_sup inf_le_right
      (conjugate_le_of_normalizes (F.monotone (by omega)) g hgG)

private theorem centerIn_mono_of_le (A B : Subgroup G) (hAB : A ≤ B)
    (hZA : centerIn B ≤ A) : centerIn B ≤ centerIn A := by
  rw [centerIn_eq A]
  exact le_inf hZA ((centerIn_centralizes B).trans (centralizer_le hAB))

private theorem map_mem_center {J K : Type*} [Group J] [Group K]
    (f : J →* K) (hf : Function.Surjective f) {z : J} (hz : z ∈ center J) :
    f z ∈ center K := by
  apply mem_center_iff.mpr
  intro x
  obtain ⟨y, rfl⟩ := hf x
  simpa only [map_mul] using congrArg f (mem_center_iff.mp hz y)

private theorem symmetricThree_center_element (z : Equiv.Perm (Fin 3))
    (hz : z ∈ center (Equiv.Perm (Fin 3))) : z = 1 := by
  have hc : ∀ z : Equiv.Perm (Fin 3), (∀ y, y * z = z * y) → z = 1 := by decide
  exact hc z (mem_center_iff.mp hz)

private theorem center_le_twoCore_of_symmetricThree (I : Subgroup G)
    (e : (I ⧸ pCore 2 I) ≃* Equiv.Perm (Fin 3)) :
    centerIn I ≤ I.pCoreIn 2 := by
  rintro x ⟨z, hz, rfl⟩
  have hq := map_mem_center (QuotientGroup.mk' (pCore 2 I))
    (QuotientGroup.mk'_surjective _) hz
  have he := map_mem_center e.toMonoidHom e.surjective hq
  have h1 : QuotientGroup.mk' (pCore 2 I) z = 1 := e.injective
    ((symmetricThree_center_element _ he).trans (map_one e).symm)
  exact mem_map_of_mem I.subtype ((QuotientGroup.eq_one_iff _).mp h1)

public theorem exists_outside_plane_centralizer (F : InvariantFlag T V n) [Finite G]
    (hn : 2 ≤ n) (hcenter : V ⊓ F.ZU = F.Vi 1) :
    ∃ u ∈ F.U, u ∉ F.W := by
  by_contra h
  push Not at h
  have hpU : F.Vi 2 ≤ F.U := (F.le_seed 2).trans (le_conjugateSpanBy V F.H)
  have hpZ : F.Vi 2 ≤ F.ZU := by
    rw [ZU, centerIn_eq]
    refine le_inf hpU (le_centralizer_iff.mp ?_)
    exact fun u hu => (h u hu).2
  have hp : F.Vi 2 ≤ F.Vi 1 := by
    rw [← hcenter]
    exact le_inf (F.le_seed 2) hpZ
  have hc := card_le_of_le hp
  rw [F.card 2 hn, F.card 1 (by omega)] at hc
  norm_num at hc

/-- The center cannot survive the S₃ quotient or its natural fixed-space calculation.
The `hfix` premise is the upper inclusion of 12.8.9(3), pulled back to O₂(I₂). -/
public theorem parabolic_center_eq (F : InvariantFlag T V n)
    (L : Subgroup G) (g : G) (hgP : g ∈ F.P L)
    (hgen : F.I₂ L = F.U ⊔ conjugate F.U g)
    (e : (F.I₂ L ⧸ pCore 2 (F.I₂ L)) ≃* Equiv.Perm (Fin 3))
    [Finite G] (hn : 2 ≤ n) (hcenter : V ⊓ F.ZU = F.Vi 1)
    (hfix : ∀ a ∈ F.U, a ∉ F.W → ∀ z ∈ (F.I₂ L).pCoreIn 2,
      ⁅z, a⁆ ∈ F.E g → z ∈ F.W) :
    F.ZU ⊓ conjugate F.ZU g = centerIn (F.I₂ L) := by
  obtain ⟨u, hu, huW⟩ := F.exists_outside_plane_centralizer hn hcenter
  have hU : F.U ≤ F.I₂ L := le_conjugateSpanBy _ _
  have hUg : conjugate F.U g ≤ F.I₂ L := by rw [hgen]; exact le_sup_right
  have hzU : centerIn (F.I₂ L) ≤ F.U := by
    intro z hz
    have hc : ⁅z, u⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.mpr
      ((centerIn_centralizes (F.I₂ L) hz u (hU hu)).symm)
    exact (show F.W ≤ F.U from inf_le_left)
      (hfix u hu huW z (center_le_twoCore_of_symmetricThree _ e hz) (hc ▸ (F.E g).one_mem))
  have hZI : conjugate (centerIn (F.I₂ L)) g = centerIn (F.I₂ L) := by
    rw [← centerIn_conjugate,
      (conjugate_eq_iff (F.I₂ L) g).mpr (le_normalizer_conjugateSpanBy F.U (F.P L) hgP)]
  have hzUg : centerIn (F.I₂ L) ≤ conjugate F.U g := by
    rw [← hZI]
    exact map_mono hzU
  apply le_antisymm
  · rw [ZU, ← centerIn_conjugate, hgen]
    exact centers_le_center_join _ _
  · apply le_inf (centerIn_mono_of_le _ _ hU hzU)
    rw [ZU, ← centerIn_conjugate]
    exact centerIn_mono_of_le _ _ hUg hzUg


private theorem omega_center_inf_ne_bot [Finite G] (T : Sylow 2 G) (D : Subgroup G)
    (hDT : D ≤ T) (hn : (T : Subgroup G) ≤ normalizer (D : Set G)) (hne : D ≠ ⊥) :
    sylowOmega T ⊓ D ≠ ⊥ := by
  let N := D.subgroupOf (T : Subgroup G)
  let : N.Normal := (normal_subgroupOf_iff_le_normalizer hDT).mpr hn
  have hnne : N ≠ ⊥ := by
    intro he
    have hm := map_subgroupOf_eq_of_le hDT
    change N.map (T : Subgroup G).subtype = D at hm
    rw [he, Subgroup.map_bot] at hm
    exact hne hm.symm
  let : Fact (IsPGroup 2 T) := ⟨T.isPGroup'⟩
  obtain ⟨A, _, hAN, hAc, hAZ⟩ := exists_central_subgroup_card_eq_prime_in_normal
    (p := 2) N ((nontrivial_iff_ne_bot N).mpr hnne)
  have hAne : A ≠ ⊥ := (one_lt_card_iff_ne_bot A).mp (by omega)
  let : Nontrivial A := (nontrivial_iff_ne_bot A).mpr hAne
  obtain ⟨z, hz⟩ := exists_ne (1 : A)
  have hzD : ((z : T) : G) ∈ D := hAN z.property
  have hzZ : ((z : T) : G) ∈ centerIn (T : Subgroup G) :=
    mem_map_of_mem (T : Subgroup G).subtype (hAZ z.property)
  have hz2 : ((z : T) : G) ^ 2 = 1 := by
    have hp := pow_card_eq_one' (x := z)
    rw [hAc] at hp
    exact congrArg (fun a : A => ((a : T) : G)) hp
  have hzO : ((z : T) : G) ∈ sylowOmega T :=
    (omegaOneAmbient_le_iff _ _).mp le_rfl _ hzZ hz2
  intro he
  have hz1 : ((z : T) : G) = 1 := by
    have hm : ((z : T) : G) ∈ sylowOmega T ⊓ D := ⟨hzO, hzD⟩
    rwa [he, mem_bot] at hm
  exact hz (Subtype.ext (Subtype.ext hz1))

/-- A strict intersection supplies an involution in the center of the original Sylow T.
The two intersection identities are proved above and are discharged by the assembly. -/
private theorem strict_intersection_meets_sylowOmega (F : InvariantFlag T V n) [Finite G]
    (L : Subgroup G) (g : G) (hUT : F.U ≤ T)
    (hI : F.Gi 2 ≤ normalizer (F.I₂ L : Set G))
    (hfirst : F.ZU ⊓ conjugate F.U g = (F.ZU ⊓ conjugate F.ZU g) ⊔ F.Vi 1)
    (hsecond : F.ZU ⊓ conjugate F.ZU g = centerIn (F.I₂ L))
    (hstrict : F.Vi 1 < F.ZU ⊓ conjugate F.U g) :
    sylowOmega T ⊓ centerIn (F.I₂ L) ≠ ⊥ := by
  have hne : centerIn (F.I₂ L) ≠ ⊥ := by
    intro he
    simp only [hsecond, he, bot_sup_eq] at hfirst
    exact hstrict.ne hfirst.symm
  apply omega_center_inf_ne_bot T _ _ _ hne
  · rw [← hsecond]
    exact inf_le_left.trans ((centerIn_le F.U).trans hUT)
  · exact (F.invariant 2).trans (hI.trans (normalizer_le_centerIn_normalizer _))

/-- The product assertion in 12.8.10(5) includes the multiplication isomorphism.
No direct-product conclusion is part of the premises. -/
private theorem center_internal_direct_product (F : InvariantFlag T V n) [Finite G]
    (hn : 1 ≤ n) (L : Subgroup G) (g : G) (hgP : g ∈ F.P L)
    (hgV : g ∈ normalizer (V : Set G)) (hgH : g ∉ F.H)
    (hcenter : V ⊓ F.ZU = F.Vi 1)
    (hsecond : F.ZU ⊓ conjugate F.ZU g = centerIn (F.I₂ L))
    (hsymmetric : conjugate F.ZU g ⊓ F.U =
      (conjugate F.ZU g ⊓ F.ZU) ⊔ conjugate (F.Vi 1) g)
    (hcontained : conjugate F.ZU g ≤ F.U) :
    F.ZU = centerIn (F.I₂ L) ⊔ F.Vi 1 ∧
      Disjoint (centerIn (F.I₂ L)) (F.Vi 1) ∧
      ∃ e : centerIn (F.I₂ L) × F.Vi 1 ≃* F.ZU,
        ∀ a b, (e (a, b) : G) = (a : G) * (b : G) := by
  have hZI : conjugate (centerIn (F.I₂ L)) g⁻¹ = centerIn (F.I₂ L) := by
    rw [← centerIn_conjugate,
      (conjugate_eq_iff (F.I₂ L) g⁻¹).mpr
        (le_normalizer_conjugateSpanBy F.U (F.P L) ((F.P L).inv_mem hgP))]
  rw [inf_eq_left.mpr hcontained, inf_comm (conjugate F.ZU g), hsecond] at hsymmetric
  have he := congrArg (fun A : Subgroup G => conjugate A g⁻¹) hsymmetric
  have hcancel (A : Subgroup G) : conjugate (conjugate A g) g⁻¹ = A := by
    simpa only [inv_inv] using conjugate_conjugate_inv A g⁻¹
  have hs (A B : Subgroup G) : conjugate (A ⊔ B) g⁻¹ = conjugate A g⁻¹ ⊔ conjugate B g⁻¹ :=
    Subgroup.map_sup _ _ _
  have hj : F.ZU = centerIn (F.I₂ L) ⊔ F.Vi 1 := by
    simpa only [hs, hcancel, hZI] using he
  have hd : Disjoint (centerIn (F.I₂ L)) (F.Vi 1) := by
    rw [← hsecond]
    exact (disjoint_iff.mpr (F.point_inf_conjugate_ZU hn hcenter g hgV hgH)).symm.mono_left inf_le_right
  have hpU : F.Vi 1 ≤ F.U := (F.le_seed 1).trans (le_conjugateSpanBy V F.H)
  have hc : centerIn (F.I₂ L) ≤ centralizer (F.Vi 1 : Set G) := by
    rw [← hsecond]
    exact inf_le_left.trans ((centerIn_centralizes F.U).trans (centralizer_le hpU))
  obtain ⟨e, he⟩ := exists_mulEquiv_prod_sup_of_disjoint_of_commuting _ _ hd hc
  refine ⟨hj, hd, e.trans (MulEquiv.subgroupCongr hj.symm), ?_⟩
  exact he


private theorem center_kernel_chain (F : InvariantFlag T V n)
    [IsMulCommutative V] (L : Subgroup G) (g : G)
    (hcenter : V ⊓ F.ZU = F.Vi 1) (hcomm : ⁅F.U, F.U⁆ ≤ F.Vi 1)
    (hhat : F.X g ⊓ F.uhatAction.ker.map F.H.subtype = F.E g)
    (htilde : F.X g ⊓ (F.localTildeAction F.H le_rfl).ker.map F.H.subtype = F.E g)
    (hcore : (F.localTildeAction F.H le_rfl).ker = pCore 2 F.H)
    (hsecond : F.ZU ⊓ conjugate F.ZU g = centerIn (F.I₂ L))
    (hsymmetric : conjugate F.ZU g ⊓ F.U =
      (conjugate F.ZU g ⊓ F.ZU) ⊔ conjugate (F.Vi 1) g) :
    conjugate F.ZU g ⊓ F.uhatAction.ker.map F.H.subtype =
        conjugate F.ZU g ⊓ (F.localTildeAction F.H le_rfl).ker.map F.H.subtype ∧
      conjugate F.ZU g ⊓ (F.localTildeAction F.H le_rfl).ker.map F.H.subtype =
        conjugate F.ZU g ⊓ QH F.H ∧
      conjugate F.ZU g ⊓ QH F.H = conjugate F.ZU g ⊓ F.U ∧
      conjugate F.ZU g ⊓ F.U =
        (conjugate F.ZU g ⊓ F.ZU) ⊔ conjugate (F.Vi 1) g ∧
      (conjugate F.ZU g ⊓ F.ZU) ⊔ conjugate (F.Vi 1) g =
        centerIn (F.I₂ L) ⊔ conjugate (F.Vi 1) g ∧
      centerIn (F.I₂ L) ⊔ conjugate (F.Vi 1) g ≤ F.U := by
  have hpZ : F.Vi 1 ≤ F.ZU := by rw [← hcenter]; exact inf_le_right
  have hUhat : F.U ≤ F.uhatAction.ker.map F.H.subtype := by
    intro u hu
    refine ⟨⟨u, F.U_le_H hu⟩, ?_, rfl⟩
    exact (F.mem_uhatAction_ker_iff _).mpr fun a ha =>
      hpZ (hcomm (commutator_mem_commutator hu ha))
  have hUtile : F.U ≤ (F.localTildeAction F.H le_rfl).ker.map F.H.subtype := by
    intro u hu
    refine ⟨⟨u, F.U_le_H hu⟩, ?_, rfl⟩
    exact (F.mem_localTildeAction_ker_iff F.H le_rfl _).mpr fun a ha =>
      hcomm (commutator_mem_commutator hu ha)
  have hkernel (K : Subgroup G) (hK : F.X g ⊓ K = F.E g) (hUK : F.U ≤ K) :
      conjugate F.ZU g ⊓ K = conjugate F.ZU g ⊓ F.U := by
    apply le_antisymm _ (inf_le_inf_left _ hUK)
    rintro x ⟨hxZ, hxK⟩
    have hxE : x ∈ F.E g := hK ▸ (show x ∈ F.X g ⊓ K from
      ⟨F.conjugate_ZU_le_X g hxZ, hxK⟩)
    exact ⟨hxZ, hxE.1.1⟩
  have hh := hkernel _ hhat hUhat
  have ht := hkernel _ htilde hUtile
  have hc : (F.localTildeAction F.H le_rfl).ker.map F.H.subtype = QH F.H := by
    rw [hcore]; rfl
  have hs : (conjugate F.ZU g ⊓ F.ZU) ⊔ conjugate (F.Vi 1) g =
      centerIn (F.I₂ L) ⊔ conjugate (F.Vi 1) g := by rw [inf_comm, hsecond]
  refine ⟨hh.trans ht.symm, congrArg (fun A => conjugate F.ZU g ⊓ A) hc,
    hc ▸ ht, hsymmetric, hs, ?_⟩
  rw [← hs, ← hsymmetric]
  exact inf_le_right

/-- The intersection, center, central-involution, commutator, internal-product and
kernel calculations of 12.8.10. The extraspecial centralizer identity is the sole
new input beyond preceding 12.8.3–9; moved rank and L-centralization remain separate.
`hfix` is the upper inclusion of 12.8.9(3) on the literal core, expressed elementwise;
`hhat`, `htilde` and `hcore` are precisely 12.8.9(5) and 12.8.4(4). -/
public theorem center_and_kernel_calculations_of_centralizer_center
    (F : InvariantFlag T V n) [Finite G] [IsMulCommutative V]
    (hn : 2 ≤ n) (L : Subgroup G) (hL : L ≤ normalizer (V : Set G))
    (hcenter : V ⊓ F.ZU = F.Vi 1) (hcomm : ⁅F.U, F.U⁆ ≤ F.Vi 1)
    (hUT : F.U ≤ T) (hI : F.Gi 2 ≤ normalizer (F.I₂ L : Set G))
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    (hgen : F.I₂ L = F.U ⊔ conjugate F.U g)
    (e : (F.I₂ L ⧸ pCore 2 (F.I₂ L)) ≃* Equiv.Perm (Fin 3))
    (hfix : ∀ a ∈ F.U, a ∉ F.W → ∀ z ∈ (F.I₂ L).pCoreIn 2,
      ⁅z, a⁆ ∈ F.E g → z ∈ F.W)
    (hhat : F.X g ⊓ F.uhatAction.ker.map F.H.subtype = F.E g)
    (htilde : F.X g ⊓ (F.localTildeAction F.H le_rfl).ker.map F.H.subtype = F.E g)
    (hcore : (F.localTildeAction F.H le_rfl).ker = pCore 2 F.H)
    (hZW : centerIn F.W = F.Vi 2 ⊔ F.ZU) :
    F.ZU ⊓ conjugate F.U g = (F.ZU ⊓ conjugate F.ZU g) ⊔ F.Vi 1 ∧
    F.ZU ⊓ conjugate F.ZU g = centerIn (F.I₂ L) ∧
    (F.Vi 1 < F.ZU ⊓ conjugate F.U g → sylowOmega T ⊓ centerIn (F.I₂ L) ≠ ⊥) ∧
    ⁅F.W, conjugate F.ZU g⁆ ≤ F.ZU ⊔ F.Vi 2 ∧
    (conjugate F.ZU g ≤ F.U →
      F.ZU = centerIn (F.I₂ L) ⊔ F.Vi 1 ∧
      Disjoint (centerIn (F.I₂ L)) (F.Vi 1) ∧
      ∃ e : centerIn (F.I₂ L) × F.Vi 1 ≃* F.ZU,
        ∀ a b, (e (a, b) : G) = (a : G) * (b : G)) ∧
    (conjugate F.ZU g ⊓ F.uhatAction.ker.map F.H.subtype =
        conjugate F.ZU g ⊓ (F.localTildeAction F.H le_rfl).ker.map F.H.subtype ∧
      conjugate F.ZU g ⊓ (F.localTildeAction F.H le_rfl).ker.map F.H.subtype =
        conjugate F.ZU g ⊓ QH F.H ∧
      conjugate F.ZU g ⊓ QH F.H = conjugate F.ZU g ⊓ F.U ∧
      conjugate F.ZU g ⊓ F.U =
        (conjugate F.ZU g ⊓ F.ZU) ⊔ conjugate (F.Vi 1) g ∧
      (conjugate F.ZU g ⊓ F.ZU) ⊔ conjugate (F.Vi 1) g =
        centerIn (F.I₂ L) ⊔ conjugate (F.Vi 1) g ∧
      centerIn (F.I₂ L) ⊔ conjugate (F.Vi 1) g ≤ F.U) := by
  have hfirst := F.center_intersection hn L hL hcenter hcomm hZW g hgP hgH
  have hsecond := F.parabolic_center_eq L g hgP hgen e hn hcenter hfix
  have hsym := F.conjugate_center_intersection hn L hL hcenter hcomm hZW g hgP hgH
  refine ⟨hfirst, hsecond,
    F.strict_intersection_meets_sylowOmega L g hUT hI hfirst hsecond,
    F.center_commutator_le_plane hn L hL hcenter hcomm hZW g hgP hgH, ?_, ?_⟩
  · exact F.center_internal_direct_product (by omega) L g hgP
      (F.P_le_seed_normalizer L hL hgP) hgH hcenter hsecond hsym
  · exact F.center_kernel_chain L g hcenter hcomm hhat htilde hcore hsecond hsym

end InvariantFlag
end CFSG.Quasithin.Chapter12.Section08
