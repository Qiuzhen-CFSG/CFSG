module

public import CFSG.Quasithin.ChapterG.Section02.LinearThree.Defs
public import Theory.GroupTheory.AlmostSpecialIntersection
public import Theory.GroupTheory.IrreducibleNormalizerCore

/-!
# The triple intersection and central first layer of G.2.5

The Frattini bound in G.2.2 bounds each conjugate's derived subgroup by
its marked point. Commutator preimages extend the three resulting bounds
to I. The triple intersection is therefore normal in I. Two disjoint
points already make it elementary abelian, hence contained in O₂(I).
Irreducibility on V makes O₂(I) centralize V.

The hypotheses here are the precise earlier inputs used by this part of
the argument. The SL₃ action, generation I=LU, product factorization and
recognition of the other two layers remain obligations of G.2.5 assembly.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
G.2.5(4–5), printed p.335, PDF p.346.
-/

open Subgroup
namespace CFSG.Quasithin.ChapterG.Section02.LinearThree
open Setup
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem conjugate_derived_le {A P V : Subgroup G} (g : G)
    (hder : ⁅A, A⁆ ≤ P) (hPV : P ≤ V)
    (hg : g ∈ normalizer (V : Set G)) : ⁅conjugate A g, conjugate A g⁆ ≤ V := by
  have hVg : conjugate V g = V :=
    mem_normalizer_iff_map_conj_eq.mp ((normalizer (V : Set G)).inv_mem hg)
  have hm := map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) (hder.trans hPV)
  rw [map_commutator] at hm
  exact hm.trans hVg.le

/-- G.2.2's Frattini bound and the marked disjoint points give the actual
normal elementary triple intersection and its full I-commutator bound. -/
public theorem intersection_layer (D : Setup G) (g h : G)
    (hp : IsPGroup 2 D.U)
    (hf : (frattini D.U).map D.U.subtype ≤ D.V₁)
    (hpoint : D.V₁ ≤ D.V)
    (hIV : I D g h ≤ normalizer (D.V : Set G))
    (hg : g ∈ normalizer (D.V : Set G))
    (hh : h ∈ normalizer (D.V : Set G))
    (hdis : Disjoint D.V₁ (conjugate D.V₁ g)) :
    D.V ≤ S₂ D g h ∧ S₂ D g h ≤ S D g h ∧
    ((S₂ D g h).subgroupOf (I D g h)).Normal ∧
    ⁅S₂ D g h, I D g h⁆ ≤ D.V ∧ IsElementaryAbelian 2 (S₂ D g h) := by
  have hVU : D.V ≤ D.U := le_conjugateSpanBy _ _
  have hVconj (x : G) (hx : x ∈ normalizer (D.V : Set G)) :
      D.V ≤ conjugate D.U x := by
    have he : conjugate D.V x = D.V :=
      mem_normalizer_iff_map_conj_eq.mp ((normalizer (D.V : Set G)).inv_mem hx)
    rw [← he]
    exact map_mono hVU
  have hVE : D.V ≤ S₂ D g h :=
    le_inf (le_inf hVU (hVconj g hg)) (hVconj h hh)
  have hder := derived_le_of_frattini_image_le hp hf
  have hA : D.U ≤ commutatorPreimage (I D g h) (S₂ D g h) D.V :=
    le_commutatorPreimage (le_sup_left.trans le_sup_left)
      ((commutator_mono le_rfl (inf_le_left.trans inf_le_left)).trans (hder.trans hpoint))
  have hB : conjugate D.U g ≤ commutatorPreimage (I D g h) (S₂ D g h) D.V :=
    le_commutatorPreimage (le_sup_right.trans le_sup_left)
      ((commutator_mono le_rfl (inf_le_left.trans inf_le_right)).trans
        (conjugate_derived_le g hder hpoint hg))
  have hC : conjugate D.U h ≤ commutatorPreimage (I D g h) (S₂ D g h) D.V :=
    le_commutatorPreimage le_sup_right
      ((commutator_mono le_rfl inf_le_right).trans
        (conjugate_derived_le h hder hpoint hh))
  have hcomm : ⁅S₂ D g h, I D g h⁆ ≤ D.V := by
    rw [commutator_comm]
    exact (commutator_mono (sup_le (sup_le hA hB) hC) le_rfl).trans
      (commutator_commutatorPreimage_le _ _ _ hIV)
  have hnorm : I D g h ≤ normalizer (S₂ D g h : Set G) :=
    le_normalizer_iff_commutator_le_left.mpr (hcomm.trans hVE)
  have hEI : S₂ D g h ≤ I D g h :=
    inf_le_left.trans (inf_le_left.trans (le_sup_left.trans le_sup_left))
  let f := (MulAut.conj g⁻¹).toMonoidHom
  have hf' : (frattini (conjugate D.U g)).map (conjugate D.U g).subtype ≤
      conjugate D.V₁ g := by
    change (frattini (D.U.map f)).map (D.U.map f).subtype ≤ D.V₁.map f
    rw [frattini_image_map D.U f (MulAut.conj g⁻¹).injective]
    exact map_mono hf
  have hfrat := frattini_eq_bot_of_disjoint_images hp (hp.map f)
    (show S₂ D g h ≤ D.U from inf_le_left.trans inf_le_left)
    (show S₂ D g h ≤ D.U.map f from inf_le_left.trans inf_le_right)
    (hdis.mono hf hf')
  let : Fact (IsPGroup 2 (S₂ D g h)) :=
    ⟨hp.of_injective (inclusion (inf_le_left.trans inf_le_left)) (inclusion_injective _)⟩
  have helem : IsElementaryAbelian 2 (S₂ D g h) :=
    (frattini_eq_bot_iff_isElementaryAbelian (p := 2)).mp hfrat
  let := helem
  exact ⟨hVE, le_pCoreIn_of_normalizes (IsElementaryAbelian.isPGroup 2 _) hEI hnorm,
    (normal_subgroupOf_iff_le_normalizer hEI).mpr hnorm, hcomm, helem⟩

/-- The first layer of the three-conjugate series lies in the intrinsic
center of S. Its irreducibility input is supplied by the natural SL₃ action. -/
public theorem central_first_layer (D : Setup G) (g h : G)
    (hp : IsPGroup 2 D.U)
    (hIV : I D g h ≤ normalizer (D.V : Set G))
    (hLI : D.L ≤ I D g h)
    (hirr : ∀ A : Subgroup G, A ≤ D.V → D.L ≤ normalizer (A : Set G) →
      A = ⊥ ∨ A = D.V) :
    D.V ≤ S D g h ⊓ centralizer (S D g h : Set G) := by
  have hVU : D.V ≤ D.U := le_conjugateSpanBy _ _
  have hVI : D.V ≤ I D g h := hVU.trans (le_sup_left.trans le_sup_left)
  have hpV := hp.of_injective (inclusion hVU) (inclusion_injective hVU)
  have hc := pCoreIn_le_centralizer_of_irreducible D.V D.L (I D g h)
    hpV hVI hIV hLI hirr
  exact le_inf (le_pCoreIn_of_normalizes hpV hVI hIV) (le_centralizer_iff.mp hc)

end CFSG.Quasithin.ChapterG.Section02.LinearThree
