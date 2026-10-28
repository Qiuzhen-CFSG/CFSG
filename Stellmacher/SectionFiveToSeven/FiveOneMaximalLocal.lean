module

public import Stellmacher.SectionFiveToSeven.Defs
public import Stellmacher.ElementaryAbelianMaxOrder
public import Theory.GroupTheory.StrongEmbedding

/-!
# The consecutive-maxima package for Stellmacher (5.1)

Assume a Sylow 2-subgroup `S0` lies in a unique maximal 2-local subgroup
`M`. This module constructs the local subgroup `N` and Sylow intersection
`S` selected in the proof of Stellmacher (5.1), and packages every
consequence needed by alternative (c).

The selection uses the source-corrected three-coordinate lexicographic order:
first the maximum elementary-abelian order `a(S)`, then
`|elementaryAbelianMaxJ S|`, and finally `|S|`. It starts from the normalizer
witness supplied by failure of strong embedding, chooses a Sylow subgroup of
`N ∩ M`, and conjugates it into `S0`. Automorphism invariance preserves all
three coordinates.

For a normalizer outside `M`, a Sylow subgroup of its intersection with `M`
that contains `S0 ∩ N` is another candidate. Monotonicity of `a`, followed by
the conditional inclusion of elementary Thompson subgroups, lets the three
maxima force this candidate back to `S`. The 2-group normalizer condition
then proves the bounds for `N_H(J(S))` and `N_H(Ω₁(Z(S)))`, without using
the stronger Property Z assumption absent from `HypothesisOne`. The same
argument gives universal Sylow control and the required Section 3 `LSet`
conditions.

For (c3), set `K=N_H(O₂(P1 ⊔ P2))`, extend the given Sylow subgroup into a
Sylow subgroup `S2` of `K`, and study
`A=N_{S2}(elementaryAbelianMaxJ S)`. Here only `J(S) ≤ A` is known, so the
proof uses the stronger maximal-elementary-order comparison with precisely
that premise. The first two maxima give `J(A)=J(S)`; the p-group normalizer
condition gives `A=S2`.  This proves the general stability statement
`J(S)=J(S2)` for every two-local `K` outside `M`; comparison along `S1≤S2`
then proves the narrower (c3) conclusion.  The general statement is the
“As above” consequence used in the journal proof of (5.4).

The journal proof is on p. 27 of
`refs/latex/stellmacher-n-group.tex`. Its printed two-coordinate selection
suppresses the first invariant; the corrected choice and normalizer transfers
are explicit in Kurzweil--Stellmacher, *The Theory of Finite Groups*, Section
12.3, pp. 357--358, Lemmas 12.3.2--12.3.4.
-/

open scoped Pointwise

namespace Stellmacher.SectionsFiveToSeven

universe u

variable {H : Type u} [Group H] [Finite H]

public structure FiveOneMaximalLocalData
    (S0 : Sylow 2 H) (M : Subgroup H) where
  N : Subgroup H
  S : Subgroup H
  S_nontrivial : S ≠ ⊥
  S_le_S0 : S ≤ (S0 : Subgroup H)
  S_ne_S0 : S ≠ (S0 : Subgroup H)
  N_twoLocal : IsTwoLocal N
  N_not_le_M : ¬ N ≤ M
  S_sylow_inter : IsSylowTwoIn S (N ⊓ M)
  S_sylow_N : IsSylowTwoIn S N
  N_mem_LSet : N ∈ SectionThree.LSet (⊤ : Subgroup H) S
  normalizer_J_le_M :
    Subgroup.normalizer (elementaryAbelianMaxJ S : Set H) ≤ M
  centralizer_omega_le_M :
    Subgroup.centralizer (omegaOneCenter S : Set H) ≤ M
  sylow_of_twoLocal_not_le_M :
    ∀ K : Subgroup H, IsTwoLocal K → ¬ K ≤ M → S ≤ K →
      IsSylowTwoIn S K
  j_stable_of_twoLocal_not_le_M :
    ∀ K : Subgroup H, IsTwoLocal K → ¬ K ≤ M →
      ∀ R : Subgroup H, elementaryAbelianMaxJ S ≤ R →
        IsSylowTwoIn R K →
          elementaryAbelianMaxJ S = elementaryAbelianMaxJ R
  c3_stable :
    ∀ T : Subgroup H, elementaryAbelianMaxJ S ≤ T →
      T ≤ (S0 : Subgroup H) →
      ∀ P1 P2 : Subgroup H,
        P1 ∈ PFamily (⊤ : Subgroup H) T →
        P2 ∈ PFamily (⊤ : Subgroup H) T →
        twoCoreIn (P1 ⊔ P2) ≠ ⊥ →
        ¬ P1 ⊔ P2 ≤ M →
        ∀ S1 : Subgroup H, T ≤ S1 → IsSylowTwoIn S1 (P1 ⊔ P2) →
          elementaryAbelianMaxJ S = elementaryAbelianMaxJ S1

private structure RawCandidate (M : Subgroup H) where
  N : Subgroup H
  S : Subgroup H
  N_twoLocal : IsTwoLocal N
  N_not_le_M : ¬ N ≤ M
  S_sylow_inter : IsSylowTwoIn S (N ⊓ M)
  S_nontrivial : S ≠ ⊥

private instance (M : Subgroup H) : Finite (RawCandidate M) := by
  let f : RawCandidate M → Subgroup H × Subgroup H := fun c => (c.N, c.S)
  apply Finite.of_injective f
  intro a b hab
  cases a
  cases b
  simp only [f, Prod.mk.injEq] at hab
  cases hab.1
  cases hab.2
  rfl

private theorem maximalTwoLocal_ne_top
    (S0 : Sylow 2 H) (h : HypothesisOne H S0)
    (M : Subgroup H)
    (hM : UniqueMaximalTwoLocalContaining (S0 : Subgroup H) M) :
    M ≠ ⊤ := by
  intro hMtop
  obtain ⟨Q, hQne, hQp, hMQ⟩ := hM.1.1.prop
  have hQnormal : Q.Normal := by
    apply Subgroup.normalizer_eq_top_iff.mp
    rw [← hMQ, hMtop]
  have hQcore : Q ≤ pCore 2 H := le_sSup ⟨hQnormal, hQp⟩
  apply hQne
  rw [h.twoCore_eq_bot] at hQcore
  exact le_bot_iff.mp hQcore

private theorem candidate_nonempty
    (S0 : Sylow 2 H) (h : HypothesisOne H S0)
    (M : Subgroup H)
    (hM : UniqueMaximalTwoLocalContaining (S0 : Subgroup H) M) :
    Nonempty (RawCandidate M) := by
  have hS0ne : (S0 : Subgroup H) ≠ ⊥ :=
    Sylow.ne_bot_of_dvd_card S0 h.even_order.two_dvd
  have hMproper := maximalTwoLocal_ne_top S0 h M hM
  have hMnot : ¬ IsStronglyEmbedded M := by
    intro hstrong
    exact h.no_strongly_embedded ⟨M, hstrong⟩
  obtain ⟨Q, hQne, hQp, hQS0, hNnot⟩ :=
    exists_twoSubgroup_le_sylow_normalizer_not_le_of_not_stronglyEmbedded
      S0 hS0ne M hMproper hM.1.2 hMnot
  let N : Subgroup H := Subgroup.normalizer (Q : Set H)
  let I : Subgroup H := N ⊓ M
  have hQI : Q ≤ I := by
    exact le_inf Subgroup.le_normalizer (hQS0.trans hM.1.2)
  let QI : Subgroup I := Q.subgroupOf I
  have hQIp : IsPGroup 2 QI :=
    hQp.of_equiv (Subgroup.subgroupOfEquivOfLe hQI).symm
  obtain ⟨T, hQIT⟩ := hQIp.exists_le_sylow
  let S : Subgroup H := (T : Subgroup I).map I.subtype
  have hSylow : IsSylowTwoIn S I := by
    exact ⟨Subgroup.map_subtype_le (T : Subgroup I), T, rfl⟩
  have hQS : Q ≤ S := by
    calc
      Q = QI.map I.subtype :=
        (Subgroup.map_subgroupOf_eq_of_le hQI).symm
      _ ≤ (T : Subgroup I).map I.subtype := Subgroup.map_mono hQIT
      _ = S := rfl
  exact ⟨{
    N := N
    S := S
    N_twoLocal := ⟨Q, hQne, hQp, rfl⟩
    N_not_le_M := hNnot
    S_sylow_inter := hSylow
    S_nontrivial := fun hbot => hQne (le_bot_iff.mp (hQS.trans_eq hbot)) }⟩

omit [Finite H] in
private theorem map_internal_ambient
    (e : H ≃* H) (P : Subgroup H) (T : Subgroup P) :
    let eP : P ≃* P.map e.toMonoidHom :=
      P.equivMapOfInjective e.toMonoidHom e.injective
    (T.map eP.toMonoidHom).map (P.map e.toMonoidHom).subtype =
      (T.map P.subtype).map e.toMonoidHom := by
  dsimp only
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1

private theorem isSylowTwoIn_map_equiv
    (e : H ≃* H) (S P : Subgroup H)
    (hSylow : IsSylowTwoIn S P) :
    IsSylowTwoIn (S.map e.toMonoidHom) (P.map e.toMonoidHom) := by
  obtain ⟨hSP, T, hTmap⟩ := hSylow
  let eP : P ≃* P.map e.toMonoidHom :=
    P.equivMapOfInjective e.toMonoidHom e.injective
  have hePsur : Function.Surjective eP.toMonoidHom := eP.surjective
  let T' : Sylow 2 (P.map e.toMonoidHom) :=
    Sylow.mapSurjective hePsur T
  refine ⟨Subgroup.map_mono hSP, T', ?_⟩
  have hT' : (T' : Subgroup (P.map e.toMonoidHom)) =
      (T : Subgroup P).map eP.toMonoidHom :=
    Sylow.coe_mapSurjective hePsur T
  rw [hT', map_internal_ambient, hTmap]

omit [Finite H] in
private theorem isTwoLocal_map_equiv
    (e : H ≃* H) (N : Subgroup H) (hN : IsTwoLocal N) :
    IsTwoLocal (N.map e.toMonoidHom) := by
  obtain ⟨Q, hQne, hQp, rfl⟩ := hN
  refine ⟨Q.map e.toMonoidHom, ?_, hQp.map e.toMonoidHom, ?_⟩
  · intro hbot
    apply hQne
    exact Subgroup.map_injective (f := e.toMonoidHom) e.injective (by simpa using hbot)
  · exact Subgroup.map_equiv_normalizer_eq Q e

omit [Finite H] in
private theorem conjugate_not_le
    (M N : Subgroup H) (m : M) (hN : ¬ N ≤ M) :
    ¬ N.map (MulAut.conj (m : H)).toMonoidHom ≤ M := by
  intro hmap
  apply hN
  intro n hn
  have hconj : (m : H) * n * (m : H)⁻¹ ∈ M :=
    hmap ⟨n, hn, rfl⟩
  have hunconj := M.mul_mem (M.mul_mem (M.inv_mem m.property) hconj) m.property
  simpa [mul_assoc] using hunconj

private structure Alignment (S0 : Sylow 2 H) (M : Subgroup H)
    (source : RawCandidate M) where
  candidate : RawCandidate M
  S_le_S0 : candidate.S ≤ (S0 : Subgroup H)
  card_S_eq : Nat.card candidate.S = Nat.card source.S
  card_J_eq : Nat.card (elementaryAbelianMaxJ candidate.S) =
    Nat.card (elementaryAbelianMaxJ source.S)
  maxOrder_eq : elementaryAbelianMaxOrder candidate.S =
    elementaryAbelianMaxOrder source.S

private noncomputable def alignCandidate
    (S0 : Sylow 2 H) (M : Subgroup H) (hS0M : (S0 : Subgroup H) ≤ M)
    (c : RawCandidate M) : Alignment S0 M c := by
  have hSM : c.S ≤ M := c.S_sylow_inter.1.trans inf_le_right
  have hSp : IsPGroup 2 c.S := by
    obtain ⟨_, T, hTmap⟩ := c.S_sylow_inter
    rw [← hTmap]
    exact T.isPGroup'.map (c.N ⊓ M).subtype
  let SM : Subgroup M := c.S.subgroupOf M
  have hSMp : IsPGroup 2 SM :=
    hSp.of_equiv (Subgroup.subgroupOfEquivOfLe hSM).symm
  let P : Sylow 2 M := Classical.choose hSMp.exists_le_sylow
  have hSMP : SM ≤ (P : Subgroup M) :=
    Classical.choose_spec hSMp.exists_le_sylow
  let S0M : Sylow 2 M := S0.subtype hS0M
  let m : M := Classical.choose (MulAction.exists_smul_eq M P S0M)
  have hm : m • P = S0M :=
    Classical.choose_spec (MulAction.exists_smul_eq M P S0M)
  let e : H ≃* H := MulAut.conj (m : H)
  let N' : Subgroup H := c.N.map e.toMonoidHom
  let S' : Subgroup H := c.S.map e.toMonoidHom
  have hmapM : M.map e.toMonoidHom = M := by
    dsimp only [e]
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mp
      (Subgroup.le_normalizer m.property)
  have hmapInter : (c.N ⊓ M).map e.toMonoidHom = N' ⊓ M := by
    rw [Subgroup.map_inf c.N M e.toMonoidHom e.injective, hmapM]
  have hSylowMap := isSylowTwoIn_map_equiv e c.S (c.N ⊓ M) c.S_sylow_inter
  rw [hmapInter] at hSylowMap
  have hS'M : S' ≤ M := by
    exact Subgroup.conj_smul_le_of_le hSM m
  have hconjSM : MulAut.conj m • SM ≤ (S0M : Subgroup M) := by
    calc
      MulAut.conj m • SM ≤ MulAut.conj m • (P : Subgroup M) := by gcongr
      _ = (S0M : Subgroup M) := by
        simpa only [Sylow.coe_subgroup_smul] using
          congrArg (fun T : Sylow 2 M => (T : Subgroup M)) hm
  have hS'S0 : S' ≤ (S0 : Subgroup H) := by
    intro x hx
    have hxsub : (⟨x, hS'M hx⟩ : M) ∈ S'.subgroupOf M := hx
    have hsubeq : S'.subgroupOf M = MulAut.conj m • SM := by
      exact (Subgroup.conj_smul_subgroupOf hSM m).symm
    rw [hsubeq] at hxsub
    exact hconjSM hxsub
  refine ⟨{
    N := N'
    S := S'
    N_twoLocal := isTwoLocal_map_equiv e c.N c.N_twoLocal
    N_not_le_M := conjugate_not_le M c.N m c.N_not_le_M
    S_sylow_inter := hSylowMap
    S_nontrivial := by
      intro hbot
      apply c.S_nontrivial
      exact Subgroup.map_eq_bot_iff_of_injective c.S e.injective |>.mp hbot },
    hS'S0, ?_, ?_, ?_⟩
  · exact Subgroup.card_map_of_injective
      (K := c.S) (f := e.toMonoidHom) e.injective
  · rw [elementaryAbelianMaxJ_map_equiv]
    exact Subgroup.card_map_of_injective
      (K := elementaryAbelianMaxJ c.S) (f := e.toMonoidHom) e.injective
  · exact elementaryAbelianMaxOrder_map_equiv e c.S

private noncomputable def firstMaxRawCandidate
    (S0 : Sylow 2 H) (h : HypothesisOne H S0)
    (M : Subgroup H)
    (hM : UniqueMaximalTwoLocalContaining (S0 : Subgroup H) M) :
    RawCandidate M := by
  let _ : Nonempty (RawCandidate M) := candidate_nonempty S0 h M hM
  exact Classical.choose (Finite.exists_max
    (fun c : RawCandidate M => elementaryAbelianMaxOrder c.S))

private theorem firstMaxRawCandidate_max
    (S0 : Sylow 2 H) (h : HypothesisOne H S0)
    (M : Subgroup H)
    (hM : UniqueMaximalTwoLocalContaining (S0 : Subgroup H) M)
    (c : RawCandidate M) :
    elementaryAbelianMaxOrder c.S ≤
      elementaryAbelianMaxOrder (firstMaxRawCandidate S0 h M hM).S := by
  let _ : Nonempty (RawCandidate M) := candidate_nonempty S0 h M hM
  exact Classical.choose_spec (Finite.exists_max
    (fun c : RawCandidate M => elementaryAbelianMaxOrder c.S)) c

private structure FirstMaxRawCandidate
    (S0 : Sylow 2 H) (h : HypothesisOne H S0)
    (M : Subgroup H)
    (hM : UniqueMaximalTwoLocalContaining (S0 : Subgroup H) M) where
  candidate : RawCandidate M
  is_first_max :
    elementaryAbelianMaxOrder candidate.S =
      elementaryAbelianMaxOrder (firstMaxRawCandidate S0 h M hM).S

private instance
    (S0 : Sylow 2 H) (h : HypothesisOne H S0)
    (M : Subgroup H)
    (hM : UniqueMaximalTwoLocalContaining (S0 : Subgroup H) M) :
    Finite (FirstMaxRawCandidate S0 h M hM) := by
  let f : FirstMaxRawCandidate S0 h M hM → RawCandidate M := fun c => c.candidate
  apply Finite.of_injective f
  intro a b hab
  cases a
  cases b
  simp only [f] at hab
  cases hab
  rfl

private instance
    (S0 : Sylow 2 H) (h : HypothesisOne H S0)
    (M : Subgroup H)
    (hM : UniqueMaximalTwoLocalContaining (S0 : Subgroup H) M) :
    Nonempty (FirstMaxRawCandidate S0 h M hM) :=
  ⟨⟨firstMaxRawCandidate S0 h M hM, rfl⟩⟩

private noncomputable def secondMaxRawCandidate
    (S0 : Sylow 2 H) (h : HypothesisOne H S0)
    (M : Subgroup H)
    (hM : UniqueMaximalTwoLocalContaining (S0 : Subgroup H) M) :
    FirstMaxRawCandidate S0 h M hM :=
  Classical.choose (Finite.exists_max
    (fun c : FirstMaxRawCandidate S0 h M hM =>
      Nat.card (elementaryAbelianMaxJ c.candidate.S)))

private theorem secondMaxRawCandidate_max
    (S0 : Sylow 2 H) (h : HypothesisOne H S0)
    (M : Subgroup H)
    (hM : UniqueMaximalTwoLocalContaining (S0 : Subgroup H) M)
    (c : FirstMaxRawCandidate S0 h M hM) :
    Nat.card (elementaryAbelianMaxJ c.candidate.S) ≤
      Nat.card (elementaryAbelianMaxJ
        (secondMaxRawCandidate S0 h M hM).candidate.S) := by
  exact Classical.choose_spec (Finite.exists_max
    (fun c : FirstMaxRawCandidate S0 h M hM =>
      Nat.card (elementaryAbelianMaxJ c.candidate.S))) c

private structure SecondMaxRawCandidate
    (S0 : Sylow 2 H) (h : HypothesisOne H S0)
    (M : Subgroup H)
    (hM : UniqueMaximalTwoLocalContaining (S0 : Subgroup H) M) where
  candidate : FirstMaxRawCandidate S0 h M hM
  is_second_max :
    Nat.card (elementaryAbelianMaxJ candidate.candidate.S) =
      Nat.card (elementaryAbelianMaxJ
        (secondMaxRawCandidate S0 h M hM).candidate.S)

private instance
    (S0 : Sylow 2 H) (h : HypothesisOne H S0)
    (M : Subgroup H)
    (hM : UniqueMaximalTwoLocalContaining (S0 : Subgroup H) M) :
    Finite (SecondMaxRawCandidate S0 h M hM) := by
  let f : SecondMaxRawCandidate S0 h M hM →
      FirstMaxRawCandidate S0 h M hM := fun c => c.candidate
  apply Finite.of_injective f
  intro a b hab
  cases a
  cases b
  simp only [f] at hab
  cases hab
  rfl

private instance
    (S0 : Sylow 2 H) (h : HypothesisOne H S0)
    (M : Subgroup H)
    (hM : UniqueMaximalTwoLocalContaining (S0 : Subgroup H) M) :
    Nonempty (SecondMaxRawCandidate S0 h M hM) :=
  ⟨⟨secondMaxRawCandidate S0 h M hM, rfl⟩⟩

private noncomputable def selectedRawCandidate
    (S0 : Sylow 2 H) (h : HypothesisOne H S0)
    (M : Subgroup H)
    (hM : UniqueMaximalTwoLocalContaining (S0 : Subgroup H) M) :
    SecondMaxRawCandidate S0 h M hM :=
  Classical.choose (Finite.exists_max
    (fun c : SecondMaxRawCandidate S0 h M hM =>
      Nat.card c.candidate.candidate.S))

private theorem selectedRawCandidate_third_max
    (S0 : Sylow 2 H) (h : HypothesisOne H S0)
    (M : Subgroup H)
    (hM : UniqueMaximalTwoLocalContaining (S0 : Subgroup H) M)
    (c : SecondMaxRawCandidate S0 h M hM) :
    Nat.card c.candidate.candidate.S ≤
      Nat.card (selectedRawCandidate S0 h M hM).candidate.candidate.S := by
  exact Classical.choose_spec (Finite.exists_max
    (fun c : SecondMaxRawCandidate S0 h M hM =>
      Nat.card c.candidate.candidate.S)) c

private noncomputable def selectedAlignment
    (S0 : Sylow 2 H) (h : HypothesisOne H S0)
    (M : Subgroup H)
    (hM : UniqueMaximalTwoLocalContaining (S0 : Subgroup H) M) :
    Alignment S0 M (selectedRawCandidate S0 h M hM).candidate.candidate :=
  alignCandidate S0 M hM.1.2
    (selectedRawCandidate S0 h M hM).candidate.candidate

private theorem selectedAlignment_first_max
    (S0 : Sylow 2 H) (h : HypothesisOne H S0)
    (M : Subgroup H)
    (hM : UniqueMaximalTwoLocalContaining (S0 : Subgroup H) M)
    (c : RawCandidate M) :
    elementaryAbelianMaxOrder c.S ≤
      elementaryAbelianMaxOrder
        (selectedAlignment S0 h M hM).candidate.S := by
  calc
    elementaryAbelianMaxOrder c.S ≤
        elementaryAbelianMaxOrder
          (firstMaxRawCandidate S0 h M hM).S :=
      firstMaxRawCandidate_max S0 h M hM c
    _ = elementaryAbelianMaxOrder
          (selectedRawCandidate S0 h M hM).candidate.candidate.S :=
      (selectedRawCandidate S0 h M hM).candidate.is_first_max.symm
    _ = elementaryAbelianMaxOrder
          (selectedAlignment S0 h M hM).candidate.S :=
      (selectedAlignment S0 h M hM).maxOrder_eq.symm

private theorem selectedAlignment_second_max
    (S0 : Sylow 2 H) (h : HypothesisOne H S0)
    (M : Subgroup H)
    (hM : UniqueMaximalTwoLocalContaining (S0 : Subgroup H) M)
    (c : RawCandidate M)
    (hmaxOrder : elementaryAbelianMaxOrder c.S =
      elementaryAbelianMaxOrder
        (selectedAlignment S0 h M hM).candidate.S) :
    Nat.card (elementaryAbelianMaxJ c.S) ≤
      Nat.card (elementaryAbelianMaxJ
        (selectedAlignment S0 h M hM).candidate.S) := by
  let cFirst : FirstMaxRawCandidate S0 h M hM := ⟨c, ?_⟩
  · calc
      Nat.card (elementaryAbelianMaxJ c.S) ≤
          Nat.card (elementaryAbelianMaxJ
            (secondMaxRawCandidate S0 h M hM).candidate.S) :=
        secondMaxRawCandidate_max S0 h M hM cFirst
      _ = Nat.card (elementaryAbelianMaxJ
            (selectedRawCandidate S0 h M hM).candidate.candidate.S) :=
        (selectedRawCandidate S0 h M hM).is_second_max.symm
      _ = Nat.card (elementaryAbelianMaxJ
            (selectedAlignment S0 h M hM).candidate.S) :=
        (selectedAlignment S0 h M hM).card_J_eq.symm
  · calc
      elementaryAbelianMaxOrder c.S =
          elementaryAbelianMaxOrder
            (selectedAlignment S0 h M hM).candidate.S := hmaxOrder
      _ = elementaryAbelianMaxOrder
            (selectedRawCandidate S0 h M hM).candidate.candidate.S :=
        (selectedAlignment S0 h M hM).maxOrder_eq
      _ = elementaryAbelianMaxOrder
            (firstMaxRawCandidate S0 h M hM).S :=
        (selectedRawCandidate S0 h M hM).candidate.is_first_max

private theorem selectedAlignment_third_max
    (S0 : Sylow 2 H) (h : HypothesisOne H S0)
    (M : Subgroup H)
    (hM : UniqueMaximalTwoLocalContaining (S0 : Subgroup H) M)
    (c : RawCandidate M)
    (hmaxOrder : elementaryAbelianMaxOrder c.S =
      elementaryAbelianMaxOrder
        (selectedAlignment S0 h M hM).candidate.S)
    (hJcard : Nat.card (elementaryAbelianMaxJ c.S) =
      Nat.card (elementaryAbelianMaxJ
        (selectedAlignment S0 h M hM).candidate.S)) :
    Nat.card c.S ≤
      Nat.card (selectedAlignment S0 h M hM).candidate.S := by
  let cFirst : FirstMaxRawCandidate S0 h M hM := ⟨c, ?_⟩
  let cSecond : SecondMaxRawCandidate S0 h M hM := ⟨cFirst, ?_⟩
  · calc
      Nat.card c.S ≤
          Nat.card (selectedRawCandidate S0 h M hM).candidate.candidate.S :=
        selectedRawCandidate_third_max S0 h M hM cSecond
      _ = Nat.card (selectedAlignment S0 h M hM).candidate.S :=
        (selectedAlignment S0 h M hM).card_S_eq.symm
  · calc
      Nat.card (elementaryAbelianMaxJ c.S) =
          Nat.card (elementaryAbelianMaxJ
            (selectedAlignment S0 h M hM).candidate.S) := hJcard
      _ = Nat.card (elementaryAbelianMaxJ
            (selectedRawCandidate S0 h M hM).candidate.candidate.S) :=
        (selectedAlignment S0 h M hM).card_J_eq
      _ = Nat.card (elementaryAbelianMaxJ
            (secondMaxRawCandidate S0 h M hM).candidate.S) :=
        (selectedRawCandidate S0 h M hM).is_second_max
  · calc
      elementaryAbelianMaxOrder c.S =
          elementaryAbelianMaxOrder
            (selectedAlignment S0 h M hM).candidate.S := hmaxOrder
      _ = elementaryAbelianMaxOrder
            (selectedRawCandidate S0 h M hM).candidate.candidate.S :=
        (selectedAlignment S0 h M hM).maxOrder_eq
      _ = elementaryAbelianMaxOrder
            (firstMaxRawCandidate S0 h M hM).S :=
        (selectedRawCandidate S0 h M hM).candidate.is_first_max

private theorem selectedAlignment_S_ne_S0
    (S0 : Sylow 2 H) (h : HypothesisOne H S0)
    (M : Subgroup H)
    (hM : UniqueMaximalTwoLocalContaining (S0 : Subgroup H) M) :
    (selectedAlignment S0 h M hM).candidate.S ≠ (S0 : Subgroup H) := by
  let d := (selectedAlignment S0 h M hM).candidate
  intro hS
  obtain ⟨M', hNM', hM'max⟩ := Finite.exists_le_maximal d.N_twoLocal
  have hS0M' : (S0 : Subgroup H) ≤ M' := by
    rw [← hS]
    exact d.S_sylow_inter.1.trans inf_le_left |>.trans hNM'
  have hM'eq : M' = M := hM.2 M' ⟨hM'max, hS0M'⟩
  exact d.N_not_le_M (hNM'.trans_eq hM'eq)

omit [Finite H] in
private theorem omegaOneCenter_le (S : Subgroup H) :
    omegaOneCenter S ≤ S := by
  unfold omegaOneCenter
  exact (Subgroup.map_mono (Subgroup.map_subtype_le _)).trans
    (Subgroup.map_subtype_le _)

omit [Finite H] in
private theorem omegaOneCenter_isElementaryAbelian (S : Subgroup H) :
    IsElementaryAbelian 2 (omegaOneCenter S) := by
  unfold omegaOneCenter
  exact ((IsElementaryAbelian.omega₁_of_isMulCommutative
    (p := 2) (Subgroup.center S)).map
      (Subgroup.center S).subtype).map S.subtype

private theorem omegaOneCenter_ne_bot_of_isPGroup
    (S : Subgroup H) (hSp : IsPGroup 2 S) (hSne : S ≠ ⊥) :
    omegaOneCenter S ≠ ⊥ := by
  let _ : Nontrivial S :=
    (Subgroup.nontrivial_iff_ne_bot S).2 hSne
  let _ : Nontrivial (Subgroup.center S) := hSp.center_nontrivial
  have hcenterP : IsPGroup 2 (Subgroup.center S) :=
    hSp.to_subgroup (Subgroup.center S)
  obtain ⟨n, hn, hcard⟩ := hcenterP.nontrivial_iff_card.mp inferInstance
  have hdvd : 2 ∣ Nat.card (Subgroup.center S) := by
    rw [hcard]
    exact dvd_pow_self 2 (Nat.pos_iff_ne_zero.mp hn)
  have hinner := omega₁_map_subtype_ne_bot
    (G := S) (Subgroup.center S) 2 hdvd
  intro hz
  apply hinner
  apply (Subgroup.map_eq_bot_iff_of_injective
    (H := (omega₁ (G := Subgroup.center S) (p := 2)).map
      (Subgroup.center S).subtype)
    (f := S.subtype) S.subtype_injective).mp
  simpa [omegaOneCenter] using hz

omit [Finite H] in
private theorem normalizer_le_normalizer_of_characteristic_internal
    (S : Subgroup H) (K : Subgroup S) [K.Characteristic] :
    Subgroup.normalizer (S : Set H) ≤
      Subgroup.normalizer (K.map S.subtype : Set H) := by
  intro x hx
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  let nx : Subgroup.normalizer (S : Set H) := ⟨x, hx⟩
  let e : S ≃* S := S.normalizerMonoidHom nx
  have hKmap : K.map e.toMonoidHom = K :=
    Subgroup.characteristic_iff_map_eq.mp inferInstance e
  calc
    (K.map S.subtype).map (MulAut.conj x).toMonoidHom =
        (K.map e.toMonoidHom).map S.subtype := by
      rw [Subgroup.map_map, Subgroup.map_map]
      congr 1
    _ = K.map S.subtype := by rw [hKmap]

omit [Finite H] in
private theorem normalizer_le_normalizer_omegaOneCenter (S : Subgroup H) :
    Subgroup.normalizer (S : Set H) ≤
      Subgroup.normalizer (omegaOneCenter S : Set H) := by
  let C : Subgroup S := Subgroup.center S
  let W : Subgroup S :=
    (omega₁ (G := C) (p := 2)).map C.subtype
  let _ : C.Characteristic := Subgroup.centerCharacteristic
  let _ : (omega₁ (G := C) (p := 2)).Characteristic :=
    omega₁_characteristic C
  let _ : W.Characteristic := inferInstance
  change Subgroup.normalizer (S : Set H) ≤
    Subgroup.normalizer (W.map S.subtype : Set H)
  exact normalizer_le_normalizer_of_characteristic_internal S W

omit [Finite H] in
private theorem elementaryAbelianMaxJ_le (S : Subgroup H) :
    elementaryAbelianMaxJ S ≤ S := by
  exact sSup_le fun _ hA => hA.1

private theorem elementaryAbelianMaxJ_ne_bot_of_isPGroup
    (S : Subgroup H) (hSp : IsPGroup 2 S) (hSne : S ≠ ⊥) :
    elementaryAbelianMaxJ S ≠ ⊥ := by
  let A : Subgroup H :=
    Classical.choose (elementaryAbelianMaxSubgroups_nonempty S)
  have hA : A ∈ elementaryAbelianMaxSubgroups S :=
    Classical.choose_spec (elementaryAbelianMaxSubgroups_nonempty S)
  have hZne := omegaOneCenter_ne_bot_of_isPGroup S hSp hSne
  have hZcard : Nat.card (omegaOneCenter S) ≤ Nat.card A :=
    hA.2.2 (omegaOneCenter S) (omegaOneCenter_le S)
      (omegaOneCenter_isElementaryAbelian S)
  have hAne : A ≠ ⊥ := by
    intro hAbot
    rw [hAbot] at hZcard
    have hZone : 1 < Nat.card (omegaOneCenter S) :=
      (Subgroup.one_lt_card_iff_ne_bot (omegaOneCenter S)).2 hZne
    have hZleOne : Nat.card (omegaOneCenter S) ≤ 1 := by
      simpa using hZcard
    exact (not_lt_of_ge hZleOne) hZone
  intro hJbot
  apply hAne
  exact le_bot_iff.mp ((le_sSup hA).trans_eq hJbot)

omit [Finite H] in
private theorem normalizer_le_normalizer_J (S : Subgroup H) :
    Subgroup.normalizer (S : Set H) ≤
      Subgroup.normalizer (elementaryAbelianMaxJ S : Set H) := by
  intro x hx
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  have hS := Subgroup.mem_normalizer_iff_map_conj_eq.mp hx
  have hJ := elementaryAbelianMaxJ_map_equiv (MulAut.conj x) S
  change S.map (MulAut.conj x).toMonoidHom = S at hS
  rw [hS] at hJ
  exact hJ.symm

private theorem exists_normalizer_element_outside
    (S0 : Sylow 2 H) (S : Subgroup H)
    (hSle : S ≤ (S0 : Subgroup H)) (hSne : S ≠ (S0 : Subgroup H)) :
    ∃ x : H, x ∈ (S0 : Subgroup H) ∧
      x ∈ Subgroup.normalizer (S : Set H) ∧ x ∉ S := by
  let A : Subgroup S0 := S.subgroupOf (S0 : Subgroup H)
  have hAproper : A < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro htop
    apply hSne
    exact le_antisymm hSle (Subgroup.subgroupOf_eq_top.mp htop)
  let _ : Group.IsNilpotent S0 := S0.isPGroup'.isNilpotent
  have hAlt : A < Subgroup.normalizer A :=
    Group.normalizerCondition_of_isNilpotent A hAproper
  obtain ⟨x, hxnorm, hxnot⟩ := SetLike.exists_of_lt hAlt
  refine ⟨(x : H), x.property, ?_, ?_⟩
  · have hxsub : x ∈
        (Subgroup.normalizer (S : Set H)).subgroupOf (S0 : Subgroup H) := by
      rw [Subgroup.subgroupOf_normalizer_eq hSle]
      exact hxnorm
    exact hxsub
  · exact hxnot

private theorem exists_normalizer_element_outside_pGroup
    (P S : Subgroup H) (hPp : IsPGroup 2 P)
    (hSP : S ≤ P) (hSne : S ≠ P) :
    ∃ x : H, x ∈ P ∧
      x ∈ Subgroup.normalizer (S : Set H) ∧ x ∉ S := by
  let A : Subgroup P := S.subgroupOf P
  have hAproper : A < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro htop
    apply hSne
    exact le_antisymm hSP (Subgroup.subgroupOf_eq_top.mp htop)
  let _ : Group.IsNilpotent P := hPp.isNilpotent
  have hAlt : A < Subgroup.normalizer A :=
    Group.normalizerCondition_of_isNilpotent A hAproper
  obtain ⟨x, hxnorm, hxnot⟩ := SetLike.exists_of_lt hAlt
  refine ⟨(x : H), x.property, ?_, ?_⟩
  · have hxsub : x ∈
        (Subgroup.normalizer (S : Set H)).subgroupOf P := by
      rw [Subgroup.subgroupOf_normalizer_eq hSP]
      exact hxnorm
    exact hxsub
  · exact hxnot

omit [Finite H] in
private theorem pSubgroup_eq_of_sylowTwoIn
    (S K X : Subgroup H) (hSylow : IsSylowTwoIn S K)
    (hXK : X ≤ K) (hSX : S ≤ X) (hXp : IsPGroup 2 X) : X = S := by
  obtain ⟨-, T, hTmap⟩ := hSylow
  let XK : Subgroup K := X.subgroupOf K
  have hXKp : IsPGroup 2 XK :=
    hXp.of_equiv (Subgroup.subgroupOfEquivOfLe hXK).symm
  have hTX : (T : Subgroup K) ≤ XK := by
    apply Subgroup.map_subtype_le_map_subtype.mp
    rw [hTmap, Subgroup.map_subgroupOf_eq_of_le hXK]
    exact hSX
  have hXeq : XK = (T : Subgroup K) := T.is_maximal' hXKp hTX
  calc
    X = XK.map K.subtype := (Subgroup.map_subgroupOf_eq_of_le hXK).symm
    _ = (T : Subgroup K).map K.subtype :=
      congrArg (fun Y : Subgroup K => Y.map K.subtype) hXeq
    _ = S := hTmap

private theorem selected_normalizer_le_M
    (S0 : Sylow 2 H) (h : HypothesisOne H S0)
    (M : Subgroup H)
    (hM : UniqueMaximalTwoLocalContaining (S0 : Subgroup H) M)
    (Q : Subgroup H) (hQne : Q ≠ ⊥) (hQp : IsPGroup 2 Q)
    (hnorm : Subgroup.normalizer
      ((selectedAlignment S0 h M hM).candidate.S : Set H) ≤
        Subgroup.normalizer (Q : Set H)) :
    Subgroup.normalizer (Q : Set H) ≤ M := by
  let d := (selectedAlignment S0 h M hM).candidate
  let K : Subgroup H := Subgroup.normalizer (Q : Set H)
  by_contra hKnot
  have hKlocal : IsTwoLocal K := ⟨Q, hQne, hQp, rfl⟩
  have hSK : d.S ≤ K := Subgroup.le_normalizer.trans hnorm
  have hSM : d.S ≤ M :=
    (selectedAlignment S0 h M hM).S_le_S0.trans hM.1.2
  let I : Subgroup H := K ⊓ M
  have hSI : d.S ≤ I := le_inf hSK hSM
  let X : Subgroup H := (S0 : Subgroup H) ⊓ I
  have hXI : X ≤ I := inf_le_right
  have hSX : d.S ≤ X :=
    le_inf (selectedAlignment S0 h M hM).S_le_S0 hSI
  have hXp : IsPGroup 2 X := S0.isPGroup'.to_le inf_le_left
  let XI : Subgroup I := X.subgroupOf I
  have hXIp : IsPGroup 2 XI :=
    hXp.of_equiv (Subgroup.subgroupOfEquivOfLe hXI).symm
  obtain ⟨R0, hXIR0⟩ := hXIp.exists_le_sylow
  let R : Subgroup H := (R0 : Subgroup I).map I.subtype
  have hSylowR : IsSylowTwoIn R I :=
    ⟨Subgroup.map_subtype_le _, R0, rfl⟩
  have hXR : X ≤ R := by
    calc
      X = XI.map I.subtype :=
        (Subgroup.map_subgroupOf_eq_of_le hXI).symm
      _ ≤ (R0 : Subgroup I).map I.subtype := Subgroup.map_mono hXIR0
      _ = R := rfl
  have hSR : d.S ≤ R := hSX.trans hXR
  let c : RawCandidate M :=
    { N := K
      S := R
      N_twoLocal := hKlocal
      N_not_le_M := hKnot
      S_sylow_inter := hSylowR
      S_nontrivial := fun hRbot =>
        d.S_nontrivial (le_bot_iff.mp (hSR.trans_eq hRbot)) }
  have haSR :=
    (elementaryAbelianMaxOrder_le_and_j_le_of_eq d.S R hSR).1
  have haRS : elementaryAbelianMaxOrder R ≤
      elementaryAbelianMaxOrder d.S :=
    selectedAlignment_first_max S0 h M hM c
  have haeq : elementaryAbelianMaxOrder R =
      elementaryAbelianMaxOrder d.S := Nat.le_antisymm haRS haSR
  have hJSR : elementaryAbelianMaxJ d.S ≤ elementaryAbelianMaxJ R :=
    (elementaryAbelianMaxOrder_le_and_j_le_of_eq d.S R hSR).2 haeq.symm
  have hJcardSR : Nat.card (elementaryAbelianMaxJ d.S) ≤
      Nat.card (elementaryAbelianMaxJ R) :=
    Subgroup.card_le_of_le hJSR
  have hJcardRS : Nat.card (elementaryAbelianMaxJ R) ≤
      Nat.card (elementaryAbelianMaxJ d.S) :=
    selectedAlignment_second_max S0 h M hM c haeq
  have hJcardEq : Nat.card (elementaryAbelianMaxJ R) =
      Nat.card (elementaryAbelianMaxJ d.S) :=
    Nat.le_antisymm hJcardRS hJcardSR
  have hRcardS : Nat.card R ≤ Nat.card d.S :=
    selectedAlignment_third_max S0 h M hM c haeq hJcardEq
  have hSeqR : d.S = R :=
    Subgroup.eq_of_le_of_card_ge hSR hRcardS
  obtain ⟨x, hxS0, hxnorm, hxnot⟩ :=
    exists_normalizer_element_outside S0 d.S
      (selectedAlignment S0 h M hM).S_le_S0
      (selectedAlignment_S_ne_S0 S0 h M hM)
  have hxK : x ∈ K := hnorm hxnorm
  have hxM : x ∈ M := hM.1.2 hxS0
  have hxI : x ∈ I := ⟨hxK, hxM⟩
  have hxX : x ∈ X := ⟨hxS0, hxI⟩
  have hxR : x ∈ R := hXR hxX
  apply hxnot
  rw [hSeqR]
  exact hxR

private theorem selected_normalizer_J_le_M
    (S0 : Sylow 2 H) (h : HypothesisOne H S0)
    (M : Subgroup H)
    (hM : UniqueMaximalTwoLocalContaining (S0 : Subgroup H) M) :
    Subgroup.normalizer
      (elementaryAbelianMaxJ
        (selectedAlignment S0 h M hM).candidate.S : Set H) ≤ M := by
  let d := (selectedAlignment S0 h M hM).candidate
  have hSp : IsPGroup 2 d.S :=
    S0.isPGroup'.to_le (selectedAlignment S0 h M hM).S_le_S0
  have hJp : IsPGroup 2 (elementaryAbelianMaxJ d.S) :=
    hSp.to_le (elementaryAbelianMaxJ_le d.S)
  have hJne :=
    elementaryAbelianMaxJ_ne_bot_of_isPGroup d.S hSp d.S_nontrivial
  exact selected_normalizer_le_M S0 h M hM
    (elementaryAbelianMaxJ d.S) hJne hJp
    (normalizer_le_normalizer_J d.S)

private theorem selected_normalizer_omega_le_M
    (S0 : Sylow 2 H) (h : HypothesisOne H S0)
    (M : Subgroup H)
    (hM : UniqueMaximalTwoLocalContaining (S0 : Subgroup H) M) :
    Subgroup.normalizer
      (omegaOneCenter
        (selectedAlignment S0 h M hM).candidate.S : Set H) ≤ M := by
  let d := (selectedAlignment S0 h M hM).candidate
  have hSp : IsPGroup 2 d.S :=
    S0.isPGroup'.to_le (selectedAlignment S0 h M hM).S_le_S0
  have hZp : IsPGroup 2 (omegaOneCenter d.S) :=
    hSp.to_le (omegaOneCenter_le d.S)
  have hZne := omegaOneCenter_ne_bot_of_isPGroup d.S hSp d.S_nontrivial
  exact selected_normalizer_le_M S0 h M hM
    (omegaOneCenter d.S) hZne hZp
    (normalizer_le_normalizer_omegaOneCenter d.S)

omit [Finite H] in
private theorem isPGroup_of_isSylowTwoIn
    (S K : Subgroup H) (hSylow : IsSylowTwoIn S K) :
    IsPGroup 2 S := by
  obtain ⟨-, T, rfl⟩ := hSylow
  exact T.isPGroup'.map K.subtype

private theorem selected_sylow_of_twoLocal_not_le_M
    (S0 : Sylow 2 H) (h : HypothesisOne H S0)
    (M : Subgroup H)
    (hM : UniqueMaximalTwoLocalContaining (S0 : Subgroup H) M)
    (K : Subgroup H) (hKlocal : IsTwoLocal K)
    (hKnot : ¬ K ≤ M)
    (hSK : (selectedAlignment S0 h M hM).candidate.S ≤ K) :
    IsSylowTwoIn (selectedAlignment S0 h M hM).candidate.S K := by
  let d := (selectedAlignment S0 h M hM).candidate
  have hSp : IsPGroup 2 d.S :=
    S0.isPGroup'.to_le (selectedAlignment S0 h M hM).S_le_S0
  let SK : Subgroup K := d.S.subgroupOf K
  have hSKp : IsPGroup 2 SK :=
    hSp.of_equiv (Subgroup.subgroupOfEquivOfLe hSK).symm
  obtain ⟨R0, hSKR0⟩ := hSKp.exists_le_sylow
  let R : Subgroup H := (R0 : Subgroup K).map K.subtype
  have hSR : d.S ≤ R := by
    calc
      d.S = SK.map K.subtype :=
        (Subgroup.map_subgroupOf_eq_of_le hSK).symm
      _ ≤ (R0 : Subgroup K).map K.subtype := Subgroup.map_mono hSKR0
      _ = R := rfl
  let A : Subgroup H :=
    R ⊓ Subgroup.normalizer (elementaryAbelianMaxJ d.S : Set H)
  have hSA : d.S ≤ A :=
    le_inf hSR (Subgroup.le_normalizer.trans (normalizer_le_normalizer_J d.S))
  have hAK : A ≤ K := inf_le_left.trans (Subgroup.map_subtype_le _)
  have hAM : A ≤ M :=
    inf_le_right.trans (selected_normalizer_J_le_M S0 h M hM)
  let I : Subgroup H := K ⊓ M
  have hAI : A ≤ I := le_inf hAK hAM
  have hAp : IsPGroup 2 A :=
    (R0.isPGroup'.map K.subtype).to_le inf_le_left
  let AI : Subgroup I := A.subgroupOf I
  have hAIp : IsPGroup 2 AI :=
    hAp.of_equiv (Subgroup.subgroupOfEquivOfLe hAI).symm
  obtain ⟨U0, hAIU0⟩ := hAIp.exists_le_sylow
  let U : Subgroup H := (U0 : Subgroup I).map I.subtype
  have hSylowU : IsSylowTwoIn U I :=
    ⟨Subgroup.map_subtype_le _, U0, rfl⟩
  have hAU : A ≤ U := by
    calc
      A = AI.map I.subtype :=
        (Subgroup.map_subgroupOf_eq_of_le hAI).symm
      _ ≤ (U0 : Subgroup I).map I.subtype := Subgroup.map_mono hAIU0
      _ = U := rfl
  have hSU : d.S ≤ U := hSA.trans hAU
  let c : RawCandidate M :=
    { N := K
      S := U
      N_twoLocal := hKlocal
      N_not_le_M := hKnot
      S_sylow_inter := hSylowU
      S_nontrivial := fun hUbot =>
        d.S_nontrivial (le_bot_iff.mp (hSU.trans_eq hUbot)) }
  have haSU :=
    (elementaryAbelianMaxOrder_le_and_j_le_of_eq d.S U hSU).1
  have haUS : elementaryAbelianMaxOrder U ≤
      elementaryAbelianMaxOrder d.S :=
    selectedAlignment_first_max S0 h M hM c
  have haeq : elementaryAbelianMaxOrder U =
      elementaryAbelianMaxOrder d.S := Nat.le_antisymm haUS haSU
  have hJSU : elementaryAbelianMaxJ d.S ≤ elementaryAbelianMaxJ U :=
    (elementaryAbelianMaxOrder_le_and_j_le_of_eq d.S U hSU).2 haeq.symm
  have hJcardSU : Nat.card (elementaryAbelianMaxJ d.S) ≤
      Nat.card (elementaryAbelianMaxJ U) := Subgroup.card_le_of_le hJSU
  have hJcardUS : Nat.card (elementaryAbelianMaxJ U) ≤
      Nat.card (elementaryAbelianMaxJ d.S) :=
    selectedAlignment_second_max S0 h M hM c haeq
  have hJcardEq : Nat.card (elementaryAbelianMaxJ U) =
      Nat.card (elementaryAbelianMaxJ d.S) :=
    Nat.le_antisymm hJcardUS hJcardSU
  have hUcardS : Nat.card U ≤ Nat.card d.S :=
    selectedAlignment_third_max S0 h M hM c haeq hJcardEq
  have hSeqU : d.S = U :=
    Subgroup.eq_of_le_of_card_ge hSU hUcardS
  have hAeqS : A = d.S := by
    apply le_antisymm
    · rw [hSeqU]
      exact hAU
    · exact hSA
  have hRp : IsPGroup 2 R := R0.isPGroup'.map K.subtype
  have hReqS : R = d.S := by
    by_contra hRne
    obtain ⟨x, hxR, hxnormS, hxnotS⟩ :=
      exists_normalizer_element_outside_pGroup R d.S hRp hSR
        (Ne.symm hRne)
    have hxA : x ∈ A :=
      ⟨hxR, normalizer_le_normalizer_J d.S hxnormS⟩
    exact hxnotS (hAeqS ▸ hxA)
  refine ⟨hSK, R0, ?_⟩
  simpa [R] using hReqS

omit [Finite H] in
private theorem twoCoreAmbient_ne_bot_of_twoLocal
    (K : Subgroup H) (hKlocal : IsTwoLocal K) :
    twoCoreAmbient K ≠ ⊥ := by
  obtain ⟨Q, hQne, hQp, hKeq⟩ := hKlocal
  have hQK : Q ≤ K := by
    rw [hKeq]
    exact Subgroup.le_normalizer
  have hQnormal : (Q.subgroupOf K).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hQK).2 (by
      rw [hKeq])
  have hQpK : IsPGroup 2 (Q.subgroupOf K) :=
    hQp.of_equiv (Subgroup.subgroupOfEquivOfLe hQK).symm
  have hQleCore : Q ≤ twoCoreAmbient K := by
    calc
      Q = (Q.subgroupOf K).map K.subtype :=
        (Subgroup.map_subgroupOf_eq_of_le hQK).symm
      _ ≤ (pCore 2 K).map K.subtype :=
        Subgroup.map_mono (le_sSup ⟨hQnormal, hQpK⟩)
      _ = twoCoreAmbient K := rfl
  intro hcore
  exact hQne (le_bot_iff.mp (hQleCore.trans_eq hcore))

omit [Finite H] in
private theorem twoCoreAmbient_normal_subgroupOf (K : Subgroup H) :
    ((twoCoreAmbient K).subgroupOf K).Normal := by
  rw [← Subgroup.comap_subtype, twoCoreAmbient,
    Subgroup.comap_map_eq_self_of_injective K.subtype_injective]
  exact (inferInstance : (pCore 2 K).Normal)

omit [Finite H] in
private theorem le_normalizer_twoCoreAmbient (K : Subgroup H) :
    K ≤ Subgroup.normalizer (twoCoreAmbient K : Set H) := by
  exact (Subgroup.normal_subgroupOf_iff_le_normalizer
    (Subgroup.map_subtype_le (pCore 2 K))).mp
      (twoCoreAmbient_normal_subgroupOf K)

private theorem selected_N_mem_LSet
    (S0 : Sylow 2 H) (h : HypothesisOne H S0)
    (M : Subgroup H)
    (hM : UniqueMaximalTwoLocalContaining (S0 : Subgroup H) M) :
    (selectedAlignment S0 h M hM).candidate.N ∈
      SectionThree.LSet (⊤ : Subgroup H)
        (selectedAlignment S0 h M hM).candidate.S := by
  let d := (selectedAlignment S0 h M hM).candidate
  have hSN : d.S ≤ d.N := d.S_sylow_inter.1.trans inf_le_left
  have hSylowN := selected_sylow_of_twoLocal_not_le_M
    S0 h M hM d.N d.N_twoLocal d.N_not_le_M hSN
  refine ⟨le_top, hSylowN.2,
    twoCoreAmbient_ne_bot_of_twoLocal d.N d.N_twoLocal, ?_⟩
  intro hScore
  have hNnormS : d.N ≤ Subgroup.normalizer (d.S : Set H) := by
    rw [hScore]
    exact le_normalizer_twoCoreAmbient d.N
  exact d.N_not_le_M
    (hNnormS.trans (normalizer_le_normalizer_J d.S) |>.trans
      (selected_normalizer_J_le_M S0 h M hM))

private theorem selected_centralizer_omega_le_M
    (S0 : Sylow 2 H) (h : HypothesisOne H S0)
    (M : Subgroup H)
    (hM : UniqueMaximalTwoLocalContaining (S0 : Subgroup H) M) :
    Subgroup.centralizer
      (omegaOneCenter
        (selectedAlignment S0 h M hM).candidate.S : Set H) ≤ M :=
  (Subgroup.centralizer_le_normalizer _).trans
    (selected_normalizer_omega_le_M S0 h M hM)

omit [Finite H] in
private theorem twoCoreIn_isPGroup (P : Subgroup H) :
    IsPGroup 2 (twoCoreIn P) :=
  (pCore_isPGroup (p := 2) (G := P)).map P.subtype

omit [Finite H] in
private theorem twoCoreIn_normal_subgroupOf (P : Subgroup H) :
    ((twoCoreIn P).subgroupOf P).Normal := by
  rw [← Subgroup.comap_subtype, twoCoreIn,
    Subgroup.comap_map_eq_self_of_injective P.subtype_injective]
  exact (inferInstance : (pCore 2 P).Normal)

omit [Finite H] in
private theorem le_normalizer_twoCoreIn (P : Subgroup H) :
    P ≤ Subgroup.normalizer (twoCoreIn P : Set H) := by
  exact (Subgroup.normal_subgroupOf_iff_le_normalizer
    (Subgroup.map_subtype_le (pCore 2 P))).mp
      (twoCoreIn_normal_subgroupOf P)

private theorem selected_j_stable_data
    (S0 : Sylow 2 H) (h : HypothesisOne H S0)
    (M : Subgroup H)
    (hM : UniqueMaximalTwoLocalContaining (S0 : Subgroup H) M)
    (K R : Subgroup H)
    (hKlocal : IsTwoLocal K) (hKnot : ¬ K ≤ M)
    (hJR : elementaryAbelianMaxJ
      (selectedAlignment S0 h M hM).candidate.S ≤ R)
    (hSylowR : IsSylowTwoIn R K) :
    elementaryAbelianMaxOrder R = elementaryAbelianMaxOrder
        (selectedAlignment S0 h M hM).candidate.S ∧
      elementaryAbelianMaxJ
          (selectedAlignment S0 h M hM).candidate.S =
        elementaryAbelianMaxJ R := by
  let d := (selectedAlignment S0 h M hM).candidate
  have hRK : R ≤ K := hSylowR.1
  have hRp : IsPGroup 2 R := isPGroup_of_isSylowTwoIn R K hSylowR
  let A : Subgroup H :=
    R ⊓ Subgroup.normalizer (elementaryAbelianMaxJ d.S : Set H)
  have hJA : elementaryAbelianMaxJ d.S ≤ A := by
    exact le_inf hJR Subgroup.le_normalizer
  have hAK : A ≤ K := inf_le_left.trans hRK
  have hAM : A ≤ M :=
    inf_le_right.trans (selected_normalizer_J_le_M S0 h M hM)
  let I : Subgroup H := K ⊓ M
  have hAI : A ≤ I := le_inf hAK hAM
  have hAp : IsPGroup 2 A := hRp.to_le inf_le_left
  let AI : Subgroup I := A.subgroupOf I
  have hAIp : IsPGroup 2 AI :=
    hAp.of_equiv (Subgroup.subgroupOfEquivOfLe hAI).symm
  obtain ⟨U0, hAIU0⟩ := hAIp.exists_le_sylow
  let U : Subgroup H := (U0 : Subgroup I).map I.subtype
  have hSylowU : IsSylowTwoIn U I :=
    ⟨Subgroup.map_subtype_le _, U0, rfl⟩
  have hAU : A ≤ U := by
    calc
      A = AI.map I.subtype :=
        (Subgroup.map_subgroupOf_eq_of_le hAI).symm
      _ ≤ (U0 : Subgroup I).map I.subtype := Subgroup.map_mono hAIU0
      _ = U := rfl
  have hJne : elementaryAbelianMaxJ d.S ≠ ⊥ := by
    have hSp : IsPGroup 2 d.S :=
      S0.isPGroup'.to_le (selectedAlignment S0 h M hM).S_le_S0
    exact elementaryAbelianMaxJ_ne_bot_of_isPGroup d.S hSp d.S_nontrivial
  have hUne : U ≠ ⊥ := by
    intro hUbot
    apply hJne
    exact le_bot_iff.mp (hJA.trans hAU |>.trans_eq hUbot)
  let c : RawCandidate M :=
    { N := K
      S := U
      N_twoLocal := hKlocal
      N_not_le_M := hKnot
      S_sylow_inter := hSylowU
      S_nontrivial := hUne }
  have haSA :=
    (elementaryAbelianMaxOrder_le_and_j_le_of_maxJ_le d.S A hJA).1
  have haAU :=
    (elementaryAbelianMaxOrder_le_and_j_le_of_eq A U hAU).1
  have haUS : elementaryAbelianMaxOrder U ≤
      elementaryAbelianMaxOrder d.S :=
    selectedAlignment_first_max S0 h M hM c
  have haSeqA : elementaryAbelianMaxOrder d.S =
      elementaryAbelianMaxOrder A :=
    Nat.le_antisymm haSA (haAU.trans haUS)
  have haAeqU : elementaryAbelianMaxOrder A =
      elementaryAbelianMaxOrder U :=
    Nat.le_antisymm haAU (haUS.trans haSA)
  have haUeqS : elementaryAbelianMaxOrder U =
      elementaryAbelianMaxOrder d.S :=
    Nat.le_antisymm haUS (haSA.trans haAU)
  have hJSA : elementaryAbelianMaxJ d.S ≤ elementaryAbelianMaxJ A :=
    (elementaryAbelianMaxOrder_le_and_j_le_of_maxJ_le d.S A hJA).2 haSeqA
  have hJAU : elementaryAbelianMaxJ A ≤ elementaryAbelianMaxJ U :=
    (elementaryAbelianMaxOrder_le_and_j_le_of_eq A U hAU).2 haAeqU
  have hJSU : elementaryAbelianMaxJ d.S ≤ elementaryAbelianMaxJ U :=
    hJSA.trans hJAU
  have hJcardUS : Nat.card (elementaryAbelianMaxJ U) ≤
      Nat.card (elementaryAbelianMaxJ d.S) :=
    selectedAlignment_second_max S0 h M hM c haUeqS
  have hJSeqU : elementaryAbelianMaxJ d.S = elementaryAbelianMaxJ U :=
    Subgroup.eq_of_le_of_card_ge hJSU hJcardUS
  have hJAleJS : elementaryAbelianMaxJ A ≤ elementaryAbelianMaxJ d.S := by
    rw [hJSeqU]
    exact hJAU
  have hJAeqJS : elementaryAbelianMaxJ A = elementaryAbelianMaxJ d.S :=
    le_antisymm hJAleJS hJSA
  have hAR : A ≤ R := inf_le_left
  have hAeqR : A = R := by
    by_contra hAne
    obtain ⟨x, hxR, hxnormA, hxnotA⟩ :=
      exists_normalizer_element_outside_pGroup R A hRp hAR hAne
    have hxnormJ : x ∈
        Subgroup.normalizer (elementaryAbelianMaxJ d.S : Set H) := by
      have hx := normalizer_le_normalizer_J A hxnormA
      rw [hJAeqJS] at hx
      exact hx
    exact hxnotA ⟨hxR, hxnormJ⟩
  refine ⟨?_, ?_⟩
  · calc
      elementaryAbelianMaxOrder R = elementaryAbelianMaxOrder A :=
        congrArg elementaryAbelianMaxOrder hAeqR.symm
      _ = elementaryAbelianMaxOrder d.S := haSeqA.symm
  · calc
      elementaryAbelianMaxJ d.S = elementaryAbelianMaxJ A := hJAeqJS.symm
      _ = elementaryAbelianMaxJ R := congrArg elementaryAbelianMaxJ hAeqR

private theorem selected_j_stable_of_twoLocal_not_le_M
    (S0 : Sylow 2 H) (h : HypothesisOne H S0)
    (M : Subgroup H)
    (hM : UniqueMaximalTwoLocalContaining (S0 : Subgroup H) M) :
    ∀ K : Subgroup H, IsTwoLocal K → ¬ K ≤ M →
      ∀ R : Subgroup H,
        elementaryAbelianMaxJ
            (selectedAlignment S0 h M hM).candidate.S ≤ R →
          IsSylowTwoIn R K →
            elementaryAbelianMaxJ
                (selectedAlignment S0 h M hM).candidate.S =
              elementaryAbelianMaxJ R := by
  intro K hKlocal hKnot R hJR hSylowR
  exact (selected_j_stable_data S0 h M hM K R
    hKlocal hKnot hJR hSylowR).2

private theorem selected_c3_stable
    (S0 : Sylow 2 H) (h : HypothesisOne H S0)
    (M : Subgroup H)
    (hM : UniqueMaximalTwoLocalContaining (S0 : Subgroup H) M) :
    ∀ T : Subgroup H,
      elementaryAbelianMaxJ
        (selectedAlignment S0 h M hM).candidate.S ≤ T →
      T ≤ (S0 : Subgroup H) →
      ∀ P1 P2 : Subgroup H,
        P1 ∈ PFamily (⊤ : Subgroup H) T →
        P2 ∈ PFamily (⊤ : Subgroup H) T →
        twoCoreIn (P1 ⊔ P2) ≠ ⊥ →
        ¬ P1 ⊔ P2 ≤ M →
        ∀ S1 : Subgroup H, T ≤ S1 → IsSylowTwoIn S1 (P1 ⊔ P2) →
          elementaryAbelianMaxJ
            (selectedAlignment S0 h M hM).candidate.S =
              elementaryAbelianMaxJ S1 := by
  intro T hJT _hTS0 P1 P2 _hP1 _hP2 hcore hjoinNot S1 hTS1 hSylow1
  let d := (selectedAlignment S0 h M hM).candidate
  let Hstar : Subgroup H := P1 ⊔ P2
  let Q : Subgroup H := twoCoreIn Hstar
  let K : Subgroup H := Subgroup.normalizer (Q : Set H)
  have hHstarK : Hstar ≤ K := le_normalizer_twoCoreIn Hstar
  have hKlocal : IsTwoLocal K :=
    ⟨Q, hcore, twoCoreIn_isPGroup Hstar, rfl⟩
  have hKnot : ¬ K ≤ M := by
    intro hKM
    exact hjoinNot (hHstarK.trans hKM)
  have hS1K : S1 ≤ K := hSylow1.1.trans hHstarK
  have hS1p : IsPGroup 2 S1 := isPGroup_of_isSylowTwoIn S1 Hstar hSylow1
  let S1K : Subgroup K := S1.subgroupOf K
  have hS1Kp : IsPGroup 2 S1K :=
    hS1p.of_equiv (Subgroup.subgroupOfEquivOfLe hS1K).symm
  obtain ⟨S20, hS1S20⟩ := hS1Kp.exists_le_sylow
  let S2 : Subgroup H := (S20 : Subgroup K).map K.subtype
  have hS1S2 : S1 ≤ S2 := by
    calc
      S1 = S1K.map K.subtype :=
        (Subgroup.map_subgroupOf_eq_of_le hS1K).symm
      _ ≤ (S20 : Subgroup K).map K.subtype := Subgroup.map_mono hS1S20
      _ = S2 := rfl
  have hS2K : S2 ≤ K := Subgroup.map_subtype_le _
  have hS2p : IsPGroup 2 S2 := S20.isPGroup'.map K.subtype
  let A : Subgroup H :=
    S2 ⊓ Subgroup.normalizer (elementaryAbelianMaxJ d.S : Set H)
  have hJA : elementaryAbelianMaxJ d.S ≤ A := by
    refine le_inf (hJT.trans hTS1 |>.trans hS1S2) ?_
    exact Subgroup.le_normalizer
  have hAK : A ≤ K := inf_le_left.trans hS2K
  have hAM : A ≤ M :=
    inf_le_right.trans (selected_normalizer_J_le_M S0 h M hM)
  let I : Subgroup H := K ⊓ M
  have hAI : A ≤ I := le_inf hAK hAM
  have hAp : IsPGroup 2 A := hS2p.to_le inf_le_left
  let AI : Subgroup I := A.subgroupOf I
  have hAIp : IsPGroup 2 AI :=
    hAp.of_equiv (Subgroup.subgroupOfEquivOfLe hAI).symm
  obtain ⟨R0, hAIR0⟩ := hAIp.exists_le_sylow
  let R : Subgroup H := (R0 : Subgroup I).map I.subtype
  have hSylowR : IsSylowTwoIn R I :=
    ⟨Subgroup.map_subtype_le _, R0, rfl⟩
  have hAR : A ≤ R := by
    calc
      A = AI.map I.subtype :=
        (Subgroup.map_subgroupOf_eq_of_le hAI).symm
      _ ≤ (R0 : Subgroup I).map I.subtype := Subgroup.map_mono hAIR0
      _ = R := rfl
  have hJne : elementaryAbelianMaxJ d.S ≠ ⊥ := by
    have hSp : IsPGroup 2 d.S :=
      S0.isPGroup'.to_le (selectedAlignment S0 h M hM).S_le_S0
    exact elementaryAbelianMaxJ_ne_bot_of_isPGroup d.S hSp d.S_nontrivial
  have hRne : R ≠ ⊥ := by
    intro hRbot
    apply hJne
    exact le_bot_iff.mp (hJA.trans hAR |>.trans_eq hRbot)
  let c : RawCandidate M :=
    { N := K
      S := R
      N_twoLocal := hKlocal
      N_not_le_M := hKnot
      S_sylow_inter := hSylowR
      S_nontrivial := hRne }
  have haSA :=
    (elementaryAbelianMaxOrder_le_and_j_le_of_maxJ_le d.S A hJA).1
  have haAR :=
    (elementaryAbelianMaxOrder_le_and_j_le_of_eq A R hAR).1
  have haRS : elementaryAbelianMaxOrder R ≤
      elementaryAbelianMaxOrder d.S :=
    selectedAlignment_first_max S0 h M hM c
  have haSeqA : elementaryAbelianMaxOrder d.S =
      elementaryAbelianMaxOrder A :=
    Nat.le_antisymm haSA (haAR.trans haRS)
  have haAeqR : elementaryAbelianMaxOrder A =
      elementaryAbelianMaxOrder R :=
    Nat.le_antisymm haAR (haRS.trans haSA)
  have haReqS : elementaryAbelianMaxOrder R =
      elementaryAbelianMaxOrder d.S :=
    Nat.le_antisymm haRS (haSA.trans haAR)
  have hJSA : elementaryAbelianMaxJ d.S ≤ elementaryAbelianMaxJ A :=
    (elementaryAbelianMaxOrder_le_and_j_le_of_maxJ_le d.S A hJA).2 haSeqA
  have hJAR : elementaryAbelianMaxJ A ≤ elementaryAbelianMaxJ R :=
    (elementaryAbelianMaxOrder_le_and_j_le_of_eq A R hAR).2 haAeqR
  have hJSR : elementaryAbelianMaxJ d.S ≤ elementaryAbelianMaxJ R :=
    hJSA.trans hJAR
  have hJcardRS : Nat.card (elementaryAbelianMaxJ R) ≤
      Nat.card (elementaryAbelianMaxJ d.S) :=
    selectedAlignment_second_max S0 h M hM c haReqS
  have hJSeqR : elementaryAbelianMaxJ d.S = elementaryAbelianMaxJ R :=
    Subgroup.eq_of_le_of_card_ge hJSR hJcardRS
  have hJAleJS : elementaryAbelianMaxJ A ≤ elementaryAbelianMaxJ d.S := by
    rw [hJSeqR]
    exact hJAR
  have hJAeqJS : elementaryAbelianMaxJ A = elementaryAbelianMaxJ d.S :=
    le_antisymm hJAleJS hJSA
  have hAS2 : A ≤ S2 := inf_le_left
  have hAeqS2 : A = S2 := by
    by_contra hAne
    obtain ⟨x, hxS2, hxnormA, hxnotA⟩ :=
      exists_normalizer_element_outside_pGroup S2 A hS2p hAS2 hAne
    have hxnormJ : x ∈
        Subgroup.normalizer (elementaryAbelianMaxJ d.S : Set H) := by
      have hx := normalizer_le_normalizer_J A hxnormA
      rw [hJAeqJS] at hx
      exact hx
    exact hxnotA ⟨hxS2, hxnormJ⟩
  have haS2eqS : elementaryAbelianMaxOrder S2 =
      elementaryAbelianMaxOrder d.S := by
    calc
      elementaryAbelianMaxOrder S2 = elementaryAbelianMaxOrder A :=
        congrArg elementaryAbelianMaxOrder hAeqS2.symm
      _ = elementaryAbelianMaxOrder d.S := haSeqA.symm
  have hJS2eqJS : elementaryAbelianMaxJ S2 = elementaryAbelianMaxJ d.S := by
    calc
      elementaryAbelianMaxJ S2 = elementaryAbelianMaxJ A :=
        congrArg elementaryAbelianMaxJ hAeqS2.symm
      _ = elementaryAbelianMaxJ d.S := hJAeqJS
  have hJS1 : elementaryAbelianMaxJ d.S ≤ S1 := hJT.trans hTS1
  have haSS1 :=
    (elementaryAbelianMaxOrder_le_and_j_le_of_maxJ_le d.S S1 hJS1).1
  have haS1S2 :=
    (elementaryAbelianMaxOrder_le_and_j_le_of_eq S1 S2 hS1S2).1
  have haSeqS1 : elementaryAbelianMaxOrder d.S =
      elementaryAbelianMaxOrder S1 :=
    Nat.le_antisymm haSS1 (haS1S2.trans_eq haS2eqS)
  have haS1eqS2 : elementaryAbelianMaxOrder S1 =
      elementaryAbelianMaxOrder S2 := by
    rw [← haSeqS1, haS2eqS]
  have hJSleJS1 : elementaryAbelianMaxJ d.S ≤ elementaryAbelianMaxJ S1 :=
    (elementaryAbelianMaxOrder_le_and_j_le_of_maxJ_le d.S S1 hJS1).2
      haSeqS1
  have hJS1leJS2 : elementaryAbelianMaxJ S1 ≤ elementaryAbelianMaxJ S2 :=
    (elementaryAbelianMaxOrder_le_and_j_le_of_eq S1 S2 hS1S2).2
      haS1eqS2
  exact le_antisymm hJSleJS1 (hJS1leJS2.trans_eq hJS2eqJS)

public theorem exists_fiveOneMaximalLocalData
    (S0 : Sylow 2 H) (h : HypothesisOne H S0)
    (M : Subgroup H)
    (hM : UniqueMaximalTwoLocalContaining (S0 : Subgroup H) M) :
    Nonempty (FiveOneMaximalLocalData S0 M) := by
  let a := selectedAlignment S0 h M hM
  let d := a.candidate
  have hSN : d.S ≤ d.N := d.S_sylow_inter.1.trans inf_le_left
  exact ⟨{
    N := d.N
    S := d.S
    S_nontrivial := d.S_nontrivial
    S_le_S0 := a.S_le_S0
    S_ne_S0 := selectedAlignment_S_ne_S0 S0 h M hM
    N_twoLocal := d.N_twoLocal
    N_not_le_M := d.N_not_le_M
    S_sylow_inter := d.S_sylow_inter
    S_sylow_N := selected_sylow_of_twoLocal_not_le_M
      S0 h M hM d.N d.N_twoLocal d.N_not_le_M hSN
    N_mem_LSet := selected_N_mem_LSet S0 h M hM
    normalizer_J_le_M := selected_normalizer_J_le_M S0 h M hM
    centralizer_omega_le_M := selected_centralizer_omega_le_M S0 h M hM
    sylow_of_twoLocal_not_le_M := selected_sylow_of_twoLocal_not_le_M
      S0 h M hM
    j_stable_of_twoLocal_not_le_M :=
      selected_j_stable_of_twoLocal_not_le_M S0 h M hM
    c3_stable := selected_c3_stable S0 h M hM }⟩


end Stellmacher.SectionsFiveToSeven
