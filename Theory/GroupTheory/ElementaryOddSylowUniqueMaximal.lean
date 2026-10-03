module
public import Theory.Representation.ElementaryAbelianAction
public import Mathlib.RepresentationTheory.Maschke
public import Mathlib.GroupTheory.Sylow
public import Mathlib.Algebra.Group.Subgroup.Pointwise

/-!
# A unique maximal overgroup of an elementary odd-group's Sylow supplement

Let R be a normal elementary abelian three-subgroup of a finite group G,
and let a Sylow two-subgroup T satisfy R T = G. If T has exactly one
maximal overgroup, then T itself is maximal. The statement needs no separate
irreducibility, faithful-action, nontriviality, or complement assumption.

For the unique maximal overgroup M, Maschke's theorem gives a T-invariant
complement D to R intersect M inside R. Convert the elementary group to its
canonical ZMod 3 representation to obtain this complement with its actual
conjugation action. The order of T is invertible in ZMod 3. Since R is
abelian, D is normalized by both R and T, hence by G. If D T were proper,
uniqueness would put D inside M, forcing all of R inside M and contradicting
maximality. Thus D T = G. The trivial intersection D intersect M now shows
every element of M belongs to T.

This standard coprime complete-reducibility argument supplies the maximal
Sylow step for the faithful one-seven product in Stellmacher (8.4)(8),
Journal of Algebra 190 (1997), p39, refs/files/stellmacher-n-group.pdf.
Only general group and representation results are imported here.
-/

open scoped IsMulCommutative
namespace Theory.GroupTheory
universe u

private theorem invariant_complement
    {G : Type u} [Group G] [Finite G]
    (R : Subgroup G) [R.Normal] [IsElementaryAbelian 3 R]
    (T : Sylow 2 G) (B : Subgroup R)
    (hB : ∀ t : T, ∀ b : R, b ∈ B →
      (MulAut.conjNormal (t : G)) b ∈ B) :
    ∃ D : Subgroup R, IsCompl B D ∧
      ∀ t : T, ∀ d : R, d ∈ D → (MulAut.conjNormal (t : G)) d ∈ D := by
  classical
  let _ : Fact (Nat.Prime 3) := ⟨by decide⟩
  let _ : MulDistribMulAction T R :=
    MulDistribMulAction.compHom R ((MulAut.conjNormal : G →* MulAut R).comp (T : Subgroup G).subtype)
  let ρ := Representation.ofElementaryAbelianAction (A := T) (G := R) (p := 3)
  have hne : (Nat.card T : ZMod 3) ≠ 0 := by
    obtain ⟨n,hn⟩ := T.isPGroup'.exists_card_eq
    rw [hn,Nat.cast_pow]
    exact pow_ne_zero _ (by decide)
  let _ : NeZero (Nat.card T : ZMod 3) := ⟨hne⟩
  let φ : AddSubgroup (Additive R) ≃o Submodule (ZMod 3) (Additive R) := AddSubgroup.toZModSubmodule 3
  let Br : Subrepresentation ρ :=
    { toSubmodule := φ B.toAddSubgroup
      apply_mem_toSubmodule := fun t b hb => hB t b hb }
  obtain ⟨Dr,hDr⟩ := exists_isCompl Br
  let D : Subgroup R := (φ.symm Dr.toSubmodule).toSubgroup
  refine ⟨D,?_,?_⟩
  · have hs : IsCompl (φ B.toAddSubgroup) Dr.toSubmodule := by
      constructor
      · rw [disjoint_iff]
        have he := congrArg Subrepresentation.toSubmodule hDr.inf_eq_bot
        exact he
      · rw [codisjoint_iff]
        have he := congrArg Subrepresentation.toSubmodule hDr.sup_eq_top
        exact he
    have ha : IsCompl B.toAddSubgroup (φ.symm Dr.toSubmodule) := by
      apply φ.isCompl_iff.mpr
      simpa only [OrderIso.apply_symm_apply] using hs
    exact IsCompl.of_orderEmbedding (RelIso.toRelEmbedding Subgroup.toAddSubgroup) ha
  · intro t d hd
    exact Dr.apply_mem_toSubmodule t hd

public theorem sylow_isCoatom_of_elementary_odd_supplement_unique_maximal
    {G : Type u} [Group G] [Finite G]
    (R : Subgroup G) [R.Normal] [IsElementaryAbelian 3 R]
    (T : Sylow 2 G) (hgen : R ⊔ (T : Subgroup G) = ⊤)
    (hunique : ∃! M : Subgroup G, IsCoatom M ∧ (T : Subgroup G) ≤ M) :
    IsCoatom (T : Subgroup G) := by
  classical
  obtain ⟨M,⟨hM,hTM⟩,huniq⟩ := hunique
  have hproper (K : Subgroup G) (hTK : (T : Subgroup G) ≤ K) (hK : K ≠ ⊤) : K ≤ M := by
    obtain ⟨N,hN,hKN⟩ := (eq_top_or_exists_le_coatom K).resolve_left hK
    exact (huniq N ⟨hN,hTK.trans hKN⟩) ▸ hKN
  let B : Subgroup R := M.subgroupOf R
  have hBn : ∀ t : T, ∀ b : R, b ∈ B → (MulAut.conjNormal (t : G)) b ∈ B := by
    intro t b hb
    exact M.mul_mem (M.mul_mem (hTM t.property) hb) (M.inv_mem (hTM t.property))
  obtain ⟨D,hBD,hDn⟩ := invariant_complement R T B hBn
  let Dg := D.map R.subtype
  have hTD : (T : Subgroup G) ≤ Subgroup.normalizer Dg := by
    apply Subgroup.le_normalizer_iff.mpr
    intro t ht d hd
    obtain ⟨d,hd,rfl⟩ := hd
    exact Subgroup.mem_map_of_mem R.subtype (hDn ⟨t,ht⟩ d hd)
  have hRD : R ≤ M ⊔ Dg := by
    rw [← Subgroup.range_subtype R,MonoidHom.range_eq_map]
    rw [← hBD.sup_eq_top,Subgroup.map_sup]
    apply sup_le _ le_sup_right
    rintro _ ⟨b,hb,rfl⟩
    exact (show M ≤ M ⊔ Dg from le_sup_left) hb
  have hDtop : Dg ⊔ (T : Subgroup G) = ⊤ := by
    by_contra hn
    have hDM : Dg ≤ M := le_sup_left.trans (hproper _ le_sup_right hn)
    have hRM : R ≤ M := hRD.trans (sup_le le_rfl hDM)
    exact hM.ne_top (top_unique (hgen ▸ sup_le hRM hTM))
  have hRnD : R ≤ Subgroup.normalizer Dg := by
    apply Subgroup.le_normalizer_iff.mpr
    intro r hr d hd
    obtain ⟨d,hd,rfl⟩ := hd
    have hc := congrArg (fun a : R => (a : G)) (mul_comm (⟨r,hr⟩ : R) d)
    change r * (d : G) = (d : G) * r at hc
    change r * (d : G) * r⁻¹ ∈ Dg
    rw [hc,mul_inv_cancel_right]
    exact Subgroup.mem_map_of_mem R.subtype hd
  have hDnG : Dg.Normal := by
    apply Subgroup.normalizer_eq_top_iff.mp
    apply top_unique
    rw [← hgen]
    exact sup_le hRnD hTD
  let _ := hDnG
  have hMeq : M = (T : Subgroup G) := by
    apply le_antisymm _ hTM
    intro m hm
    have hmem : m ∈ Dg ⊔ (T : Subgroup G) := hDtop ▸ Subgroup.mem_top _
    obtain ⟨d,hd,t,ht,hdt⟩ := Subgroup.mem_sup_of_normal_left.mp hmem
    have hdM : d ∈ M := by
      have hh := M.mul_mem hm (M.inv_mem (hTM ht))
      rw [← hdt] at hh
      simpa using hh
    have hd1 : d = 1 := by
      obtain ⟨d,hd,rfl⟩ := hd
      have hh : d ∈ B ⊓ D := ⟨hdM,hd⟩
      rw [hBD.inf_eq_bot] at hh
      exact congrArg Subtype.val hh
    simpa [← hdt,hd1] using ht
  exact hMeq ▸ hM

end Theory.GroupTheory
