module
public import Stellmacher.SectionThree.LemmaThreeFour
public import Stellmacher.BaumannIntermediate
public import Stellmacher.BaumannNormalizer
public import Stellmacher.OmegaOneCenterMap

/-!
# Residual centralization when the Thompson subgroup lies in the core

For a solvable local-family member P over S, suppose the elementary
Thompson subgroup J(S) lies in O2(P), while the Baumann subgroup B(S) does
not. Then O^2(P) centralizes the entire omega-one center of J(S). In
particular, this supplies a normal residual inside the centralizer of
every involution from that omega-center.

The maximum elementary abelian orders of O2(P) and S coincide because
J(S) lies in O2(P). Hence J(O2(P))=J(S), so its omega-center is normalized
by P. Its centralizer is therefore also normalized by P and contains B(S).
Stellmacher (3.4) gives [O^2(P),B(S)]=O^2(P), forcing the residual into
that centralizer.

This isolates the Thompson-in-core branch of the centralizer selection
in Stellmacher (6.4), Journal of Algebra 190 (1997), p32, using (3.4), p22.
Source: refs/latex/stellmacher-n-group.tex. Characteristic two and the
global Hypothesis Two context are not needed for this local implication.
-/

namespace Stellmacher.SectionThree

public theorem residual_centralizes_thompson_omega_of_le_twoCore
    {G : Type*} [Group G] [Finite G]
    (S : Subgroup G) (h : Hypotheses G S)
    (P : Subgroup G) (hP : P ∈ PSet (⊤ : Subgroup G) S)
    (hsolv : Group.IsSolvable P)
    (hB : ¬ S ⊓ Subgroup.centralizer
      (omegaOneCenterAmbient (elementaryAbelianMaxJ S) : Set G) ≤ twoCoreAmbient P)
    (hJ : elementaryAbelianMaxJ S ≤ twoCoreAmbient P) :
    twoResidualAmbient P ≤ Subgroup.centralizer
      (omegaOneCenterAmbient (elementaryAbelianMaxJ S) : Set G) := by
  let Q := twoCoreAmbient P
  let J := elementaryAbelianMaxJ S
  let Z := omegaOneCenterAmbient J
  let B := S ⊓ Subgroup.centralizer (Z : Set G)
  let C := Subgroup.centralizer (Z : Set G)
  have hQP : Q ≤ P := Subgroup.map_subtype_le _
  have hQS : Q ≤ S := by
    obtain ⟨T, hT⟩ := hP.1.2.1
    rw [← hT]
    exact Subgroup.map_mono ((pCore_isPGroup (p := 2) (G := P)).le_sylow_of_normal T)
  have hsmall := elementaryAbelianMaxOrder_le_and_j_le_of_eq Q S hQS
  have hlarge := elementaryAbelianMaxOrder_le_and_j_le_of_maxJ_le S Q hJ
  have horder : elementaryAbelianMaxOrder Q = elementaryAbelianMaxOrder S :=
    le_antisymm hsmall.1 hlarge.1
  have hJeq : elementaryAbelianMaxJ Q = J :=
    le_antisymm (hsmall.2 horder) (hlarge.2 horder.symm)
  have hQN : (Q.subgroupOf P).Normal := by
    change (((pCore 2 P).map P.subtype).subgroupOf P).Normal
    rw [subgroupOf_map_subtype_eq]
    infer_instance
  have hPNQ : P ≤ Subgroup.normalizer (Q : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hQP).mp hQN
  have hPNZ : P ≤ Subgroup.normalizer (Z : Set G) := by
    intro p hp
    apply Subgroup.mem_normalizer_iff_map_conj_eq.mpr
    have hQmap := Subgroup.mem_normalizer_iff_map_conj_eq.mp (hPNQ hp)
    change Q.map (MulAut.conj p).toMonoidHom = Q at hQmap
    change Z.map (MulAut.conj p).toMonoidHom = Z
    dsimp only [Z]
    rw [← hJeq, ← omegaOneCenterAmbient_map_injective _ (MulAut.conj p).injective,
      ← elementaryAbelianMaxJ_map_equiv (MulAut.conj p) Q, hQmap]
  have hNC : Subgroup.normalizer (Z : Set G) ≤ Subgroup.normalizer (C : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer
      (Subgroup.centralizer_le_normalizer (Z : Set G))).mp inferInstance
  have hBN : (B.subgroupOf S).Normal := by
    apply (Subgroup.normal_subgroupOf_iff_le_normalizer (show B ≤ S from inf_le_left)).mpr
    exact S.le_normalizer.trans (normalizer_le_normalizer_baumann S)
  have hRB := (lemma_three_four S h P hP B ⟨inf_le_left, hBN⟩ hsolv).resolve_left hB
  rw [← hRB]
  exact (Subgroup.commutator_mono (Subgroup.map_subtype_le _) (show B ≤ C from inf_le_right)).trans
    (Subgroup.le_normalizer_iff_commutator_le_right.mp (hPNZ.trans hNC))

end Stellmacher.SectionThree
