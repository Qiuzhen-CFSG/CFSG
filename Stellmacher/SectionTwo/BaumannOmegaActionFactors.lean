module
public import Stellmacher.SectionTwo.NormalSupplementBaumannDecomposition
public import Stellmacher.CentralizerQuotientAction

/-!
# Action factors on the Baumann omega module

Let a normal elementary abelian subgroup V lie in the ambient image B of
a Sylow subgroup Q of N. Suppose B is its own Baumann subgroup, Q normally
generates N, N is solvable, and the image of N in the centralizer quotient
of V has trivial two-core. The quotient image of Q equals its Thompson
image and the whole image of N decomposes into one-seven factors on V.
The theorem retains injective indexing, normality of every factor, and
the matching fixed-space and commutator decomposition on this exact V.

Maximal elementary subgroups of B supply offenders on V. Weak closure
of the Thompson subgroup descends from Q. The self-Baumann identity forces
B to fix the Thompson fixed space, by elementary centralizer control.
The weakly closed offender product theorem then identifies the normal
closure of the Sylow image, which is the whole image of N by hypothesis.
The action is the exact supplied centralizer quotient action, restricted
to N's image; no replacement native module or action instance is used.

Source: Stellmacher (2.2), Journal of Algebra 190 (1997), p20, applied
to the actual modules Zi in (6.3), p31. Native module and two-core transport
are supplied separately by BaumannOmegaSupplementData and
BaumannOmegaQuotientSupplement.
-/

namespace Stellmacher.SectionTwo
universe u

private theorem fixedPoints_map_subtype
    {G V : Type u} [Group G] [Group V] [MulDistribMulAction G V]
    (N : Subgroup G) (A : Subgroup N) :
    FixedPoints.subgroup (A.map N.subtype) V = FixedPoints.subgroup A V := by
  ext v
  rw [FixedPoints.mem_subgroup, FixedPoints.mem_subgroup]
  constructor
  · intro hv a
    exact hv ⟨((a : N) : G), Subgroup.mem_map_of_mem N.subtype a.property⟩
  · intro hv a
    obtain ⟨x, hx, hxa⟩ := a.property
    have h := hv ⟨x, hx⟩
    change (x : G) • v = v at h
    change (a : G) • v = v
    rw [← hxa]
    exact h

private theorem oneA_of_map_subtype
    {G V : Type u} [Group G] [Group V] [Finite G] [Finite V]
    [MulDistribMulAction G V]
    (N : Subgroup G) (S A : Subgroup N)
    (h : SectionOne.oneA (V := V) (S.map N.subtype) (A.map N.subtype)) :
    SectionOne.oneA (V := V) S A := by
  have hAS : A ≤ S := (Subgroup.map_le_map_iff_of_injective N.subtype_injective).mp h.1
  have hAe : IsElementaryAbelian 2 A := by
    let _ : IsElementaryAbelian 2 (A.map N.subtype) := h.2.1
    have hh := IsElementaryAbelian.subgroupOf (p := 2) (Subgroup.map_subtype_le A)
    rwa [subgroupOf_map_subtype_eq] at hh
  refine ⟨hAS, hAe, ?_⟩
  have hm := h.2.2
  unfold SectionOne.m at hm ⊢
  rwa [fixedPoints_map_subtype, Subgroup.card_map_of_injective N.subtype_injective] at hm

private theorem map_subgroupMap_subtype
    {G H : Type*} [Group G] [Group H] (q : G →* H)
    (N : Subgroup G) (A : Subgroup N) :
    (A.map (q.subgroupMap N)).map (N.map q).subtype = (A.map N.subtype).map q := by
  rw [Subgroup.map_map, Subgroup.map_map]
  rfl

set_option maxHeartbeats 900000 in
public theorem baumann_omega_action_factors
    {G : Type u} [Group G] [Finite G]
    (V : Subgroup G) (hVn : V.Normal) [IsElementaryAbelian 2 V]
    {barG : Type u} [Group barG] [Finite barG] (q : G →* barG)
    (hq : Function.Surjective q) (hker : q.ker = Subgroup.centralizer (V : Set G))
    (N : Subgroup G) (Q : Sylow 2 N)
    (hsolv : Group.IsSolvable N)
    (hgen : Subgroup.normalClosure ((Q : Subgroup N) : Set N) = ⊤)
    (hVQ : V ≤ (Q : Subgroup N).map N.subtype)
    (hself : ((Q : Subgroup N).map N.subtype) ⊓ Subgroup.centralizer
      (omegaOneCenterAmbient
        (elementaryAbelianMaxJ ((Q : Subgroup N).map N.subtype)) : Set G) =
      (Q : Subgroup N).map N.subtype)
    (hcore : pCore 2 (N.map q) = ⊥) :
    letI := centralizerQuotientAction V hVn q hq hker
    let f := q.subgroupMap N
    (elementaryAbelianMaxJ (Q : Subgroup N)).map f = (Q : Subgroup N).map f ∧
      ∃ (n : ℕ) (D : Fin n → Subgroup (N.map q)),
        IsInternalDirectProductFamily ⊤ D ∧ Function.Injective D ∧
        (∀ i, SectionOne.IsOneSevenFactor (V := V) (D i)) ∧
        (∀ i, (D i).Normal) ∧
        IsInternalDirectProductFamily (⊤ : Subgroup V)
          (fun i : Option (Fin n) => match i with
            | none => FixedPoints.subgroup (⊤ : Subgroup (N.map q)) V
            | some i => commutatorAction (D i) V) := by
  classical
  let _ := centralizerQuotientAction V hVn q hq hker
  let barN := N.map q
  let f : N →* barN := q.subgroupMap N
  have hf : Function.Surjective f := q.subgroupMap_surjective N
  let T : Sylow 2 barN := Q.mapSurjective hf
  let QA := (Q : Subgroup N).map N.subtype
  let J := (elementaryAbelianMaxJ (Q : Subgroup N)).map f
  let Bbar := (Q : Subgroup N).map f
  let I := {A : Subgroup G // A ∈ elementaryAbelianMaxSubgroups QA}
  let A : I → Subgroup barN := fun a => (a.val.subgroupOf N).map f
  have hQAN : QA ≤ N := Subgroup.map_subtype_le _
  have hQmap : (T : Subgroup barN).map barN.subtype = QA.map q :=
    map_subgroupMap_subtype q N (Q : Subgroup N)
  have hJmap : J.map barN.subtype = (elementaryAbelianMaxJ QA).map q := by
    rw [show J = (elementaryAbelianMaxJ (Q : Subgroup N)).map (q.subgroupMap N) from rfl,
      map_subgroupMap_subtype, ← elementaryAbelianMaxJ_map_injective N.subtype N.subtype_injective]
  have hAmap (a : I) : (A a).map barN.subtype = a.val.map q := by
    change ((a.val.subgroupOf N).map (q.subgroupMap N)).map barN.subtype = _
    rw [map_subgroupMap_subtype,
      Subgroup.map_subgroupOf_eq_of_le (a.property.1.trans hQAN)]
  have hA : ∀ a, SectionOne.oneA (V := V) (T : Subgroup barN) (A a) := by
    intro a
    apply oneA_of_map_subtype barN (T : Subgroup barN) (A a)
    rw [hQmap, hAmap]
    exact centralizerQuotientAction_maxElementary_map_mem_oneA QA V a.val hVn hVQ
      a.property q hq hker
  have hJgen : J = ⨆ a, A a := by
    apply Subgroup.map_injective barN.subtype_injective
    rw [hJmap, Subgroup.map_iSup]
    have hj : elementaryAbelianMaxJ QA = ⨆ a : I, a.val := by
      apply le_antisymm
      · exact sSup_le fun K hK => le_iSup (fun a : I => a.val) ⟨K, hK⟩
      · exact iSup_le fun a => le_sSup a.property
    rw [hj, Subgroup.map_iSup]
    exact iSup_congr fun a => (hAmap a).symm
  have hweak : ∀ g : barN, J.map (MulAut.conj g).toMonoidHom ≤ (T : Subgroup barN) →
      J.map (MulAut.conj g).toMonoidHom = J := by
    intro g hg
    exact weakly_closed_map_of_surjective Q (elementaryAbelianMaxJ (Q : Subgroup N))
      (sSup_le fun a ha => ha.1)
      (fun x hx => elementaryAbelianMaxJ_map_eq_of_le (Q : Subgroup N) (MulAut.conj x) hx)
      f hf g hg
  have hJB : J ≤ Bbar := Subgroup.map_mono (sSup_le fun _ ha => ha.1)
  have hBS : Bbar ≤ (T : Subgroup barN) := le_rfl
  have hBfix : Bbar ≤ fixingSubgroup barN (FixedPoints.subgroup J V : Set V) := by
    intro b hb
    rw [mem_fixingSubgroup_iff]
    intro v hv
    obtain ⟨b₀, hb₀, rfl⟩ := hb
    have hv' : v ∈ FixedPoints.subgroup ((elementaryAbelianMaxJ QA).map q) V := by
      rw [← hJmap, fixedPoints_map_subtype]
      exact hv
    have hvC : (v : G) ∈ Subgroup.centralizer (elementaryAbelianMaxJ QA : Set G) := by
      have hvmap : (v : G) ∈ (FixedPoints.subgroup ((elementaryAbelianMaxJ QA).map q) V).map V.subtype :=
        Subgroup.mem_map_of_mem V.subtype hv'
      rw [centralizerQuotientAction_fixedPoints_image_map V hVn q hq hker] at hvmap
      exact hvmap.2
    let _ : IsElementaryAbelian 2 (Subgroup.zpowers (v : G)) :=
      IsElementaryAbelian.zpowers_of_pow_eq_one
        (elemPow_eq_one_of_isElementaryAbelian (p := 2) (v : G) v.property)
    have hvOmega : (v : G) ∈ omegaOneCenterAmbient (elementaryAbelianMaxJ QA) :=
      elementary_centralizer_maxJ_le_omegaCenter QA (Subgroup.zpowers (v : G))
        (Subgroup.zpowers_le.mpr (hVQ v.property))
        (Subgroup.zpowers_le.mpr hvC) (Subgroup.mem_zpowers (v : G))
    have hbQA : (b₀ : G) ∈ QA := Subgroup.mem_map_of_mem N.subtype hb₀
    have hcent : QA ≤ Subgroup.centralizer
        (omegaOneCenterAmbient (elementaryAbelianMaxJ QA) : Set G) :=
      hself.symm.le.trans inf_le_right
    apply Subtype.ext
    change ((q (b₀ : G) • v : V) : G) = v
    rw [centralizerQuotientAction_smul_coe V hVn q hq hker]
    have hc := Subgroup.mem_centralizer_iff.mp (hcent hbQA) v hvOmega
    rw [← hc, mul_inv_cancel_right]
  have hfaith : fixingSubgroup barN (Set.univ : Set V) = ⊥ := by
    apply bot_unique
    intro x hx
    apply Subtype.ext
    have hx' : (x : barG) ∈ fixingSubgroup barG (Set.univ : Set V) := by
      rw [mem_fixingSubgroup_iff] at hx ⊢
      exact hx
    rw [centralizerQuotientAction_faithful V hVn q hq hker] at hx'
    exact hx'
  have hsolbar : Group.IsSolvable barN := by
    let _ := hsolv
    exact Group.isSolvable_of_surjective hf
  obtain ⟨hJeq, n, D, hDgen, hDprod, hDin, hD, hDn, hmodule⟩ :=
    SectionOne.weakly_closed_offender_baumann_product
      hsolbar hfaith hcore T A hA J Bbar hJgen hweak hJB hBS hBfix
  have htop : Subgroup.normalClosure (Bbar : Set barN) = ⊤ := by
    change Subgroup.normalClosure (f '' ((Q : Subgroup N) : Set N)) = ⊤
    rw [← Subgroup.map_normalClosure _ f hf, hgen, Subgroup.map_top_of_surjective f hf]
  rw [htop] at hDprod hDn hmodule
  refine ⟨hJeq, n, D, hDprod, hDin, hD, ?_, hmodule⟩
  intro i
  apply Subgroup.normalizer_eq_top_iff.mp
  exact top_unique ((Subgroup.normal_subgroupOf_iff_le_normalizer
    (show D i ≤ ⊤ from le_top)).mp (hDn i))

end Stellmacher.SectionTwo
