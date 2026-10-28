module

public import Stellmacher.PushingUp.AmalgamGraph
public import Stellmacher.TwoResidualSylowSupplement
public import Stellmacher.PushingUp.OmegaCenterGeneration

/-!
# Transporting base-stabilizer structure to the original group

This module identifies the distinguished `M`-vertex stabilizer in the free
amalgam with the original finite group `M`.  Under this equivalence, the
2-core, the 2-residual, and hence their commutator are carried to the
corresponding subgroups of the base stabilizer.  Elementary abelianness,
irreducibility of a section, and the full-commutator containment can therefore
be pulled back to `M`.

The transport itself is source-neutral; its immediate use is the
local-to-original bookkeeping needed after the
distance-two case of Stellmacher, *Pushing up*, Arch. Math. 46 (1986), (3.2).
Here the local subgroup is literally
`[O₂(G_a), O²(G_a)]` for the base vertex `a`; it is not identified with the
graph subgroup `vertexZ`. The natural-data companion also transports the
canonical centralizer quotient, the order-four calculation, and the exact
equality with the full-group commutator of the canonical Section Two module.
Sylow conjugacy identifies the normal closures of their omega centers, so
this transport retains the original supplied Sylow module. The base
equivalence and functoriality lemmas remain private.

The residual comparison is reconstructed from the low Huppert residual API.
Thus this module does not import the later Section Three residual development
or assume that the free amalgam or its vertex set is finite.
-/

namespace Stellmacher.PushingUp

open AmalgamGraph
open BenderSuzuki External
open scoped Pointwise

universe u v

private theorem twoResidualAmbient_top_eq_hktPResidual_low
    {G : Type u} [Group G] [Finite G] :
    twoResidualAmbient (⊤ : Subgroup G) = hktPResidual 2 G := by
  classical
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  apply le_antisymm
  · let R : Subgroup G := hktPResidual 2 G
    have hRnormal : R.Normal := hktPResidual_normal
    let _ : R.Normal := hRnormal
    have hRquot : IsPGroup 2 (G ⧸ R) := hktPResidual_quotient_isPGroup
    let Rtop : Subgroup (⊤ : Subgroup G) := R.subgroupOf ⊤
    have hRtopNormal : Rtop.Normal := hRnormal.subgroupOf ⊤
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := 2)).mp hRquot
    have hRtopIndex : Rtop.index = 2 ^ n := by
      calc
        Rtop.index = R.relIndex ⊤ := rfl
        _ = R.index := Subgroup.relIndex_top_right R
        _ = Nat.card (G ⧸ R) := Subgroup.index_eq_card R
        _ = 2 ^ n := hn
    have hRtop_mem : Rtop ∈
        {N : Subgroup (⊤ : Subgroup G) |
          N.Normal ∧ ∃ n : ℕ, N.index = 2 ^ n} :=
      ⟨hRtopNormal, n, hRtopIndex⟩
    have hsInf_le : twoResidualSubgroup (⊤ : Subgroup G) ≤ Rtop :=
      sInf_le hRtop_mem
    calc
      twoResidualAmbient (⊤ : Subgroup G) =
          (twoResidualSubgroup (⊤ : Subgroup G)).map
            (⊤ : Subgroup G).subtype := rfl
      _ ≤ Rtop.map (⊤ : Subgroup G).subtype := Subgroup.map_mono hsInf_le
      _ = R := Subgroup.map_subgroupOf_eq_of_le le_top
      _ = hktPResidual 2 G := rfl
  · intro x hx
    change x ∈ (twoResidualSubgroup (⊤ : Subgroup G)).map
      (⊤ : Subgroup G).subtype
    refine ⟨⟨x, by simp⟩, ?_, rfl⟩
    change (⟨x, by simp⟩ : (⊤ : Subgroup G)) ∈ sInf
      {N : Subgroup (⊤ : Subgroup G) |
        N.Normal ∧ ∃ n : ℕ, N.index = 2 ^ n}
    rw [Subgroup.mem_sInf]
    intro R hR
    let N : Subgroup G := R.map (⊤ : Subgroup G).subtype
    have hNnormal : N.Normal :=
      hR.1.map (⊤ : Subgroup G).subtype (fun y => ⟨⟨y, by simp⟩, rfl⟩)
    let _ : N.Normal := hNnormal
    obtain ⟨n, hn⟩ := hR.2
    have hN_eq : N.subgroupOf (⊤ : Subgroup G) = R := by
      apply Subgroup.map_injective_of_ker_le
        (f := (⊤ : Subgroup G).subtype)
        (H := N.subgroupOf ⊤) (K := R)
      · simp
      · simp
      · simp [N]
    have hNindex : N.index = 2 ^ n := by
      calc
        N.index = N.relIndex ⊤ := (Subgroup.relIndex_top_right N).symm
        _ = (N.subgroupOf (⊤ : Subgroup G)).index := rfl
        _ = R.index := by rw [hN_eq]
        _ = 2 ^ n := hn
    have hquot : IsPGroup 2 (G ⧸ N) := by
      rw [IsPGroup.iff_card]
      exact ⟨n, by simpa [← Subgroup.index_eq_card N] using hNindex⟩
    have hxN : x ∈ N := hktPResidual_le N hNnormal hquot hx
    rcases hxN with ⟨y, hy, hyx⟩
    have hy_eq : y = (⟨x, by simp⟩ : (⊤ : Subgroup G)) :=
      Subtype.ext hyx
    simpa [hy_eq] using hy

private theorem hktPResidual_le_map_equiv
    {G : Type u} {H : Type v} [Group G] [Group H] [Finite G] [Finite H]
    (e : G ≃* H) :
    hktPResidual 2 H ≤ (hktPResidual 2 G).map e.toMonoidHom := by
  let R : Subgroup G := hktPResidual 2 G
  have hRnormal : R.Normal := hktPResidual_normal
  let _ : R.Normal := hRnormal
  have hmapNormal : (R.map e.toMonoidHom).Normal :=
    hRnormal.map e.toMonoidHom e.surjective
  let _ : (R.map e.toMonoidHom).Normal := hmapNormal
  let eQ : (G ⧸ R) ≃* (H ⧸ R.map e.toMonoidHom) :=
    QuotientGroup.congr R (R.map e.toMonoidHom) e rfl
  have hquot : IsPGroup 2 (H ⧸ R.map e.toMonoidHom) :=
    (hktPResidual_quotient_isPGroup (Q := G) (q := 2)).of_equiv eQ
  exact hktPResidual_le (R.map e.toMonoidHom) hmapNormal hquot

private theorem hktPResidual_map_equiv
    {G : Type u} {H : Type v} [Group G] [Group H] [Finite G] [Finite H]
    (e : G ≃* H) :
    (hktPResidual 2 G).map e.toMonoidHom = hktPResidual 2 H := by
  apply le_antisymm
  · have hback := hktPResidual_le_map_equiv e.symm
    have hmap := Subgroup.map_mono (f := e.toMonoidHom) hback
    have hcancel : ((hktPResidual 2 H).map e.symm.toMonoidHom).map
        e.toMonoidHom = hktPResidual 2 H := by
      ext x
      simp
    exact hmap.trans_eq hcancel
  · exact hktPResidual_le_map_equiv e

private theorem twoResidualAmbient_top_map_equiv
    {G : Type u} {H : Type v} [Group G] [Group H] [Finite G] [Finite H]
    (e : G ≃* H) :
    (twoResidualAmbient (⊤ : Subgroup G)).map e.toMonoidHom =
      twoResidualAmbient (⊤ : Subgroup H) := by
  rw [twoResidualAmbient_top_eq_hktPResidual_low,
    twoResidualAmbient_top_eq_hktPResidual_low]
  exact hktPResidual_map_equiv e

private theorem isIrreducibleSection_map_equiv
    {G : Type u} {H : Type v} [Group G] [Group H]
    (e : G ≃* H) (S N K : Subgroup G)
    (h : IsIrreducibleSection S N K) :
    IsIrreducibleSection
      (S.map e.toMonoidHom) (N.map e.toMonoidHom) (K.map e.toMonoidHom) := by
  refine ⟨Subgroup.map_mono h.1, ?_, ?_⟩
  · intro hNK
    apply h.2.1
    exact e.mapSubgroup.injective hNK
  · intro A hNA hAK hAinv
    let Apre : Subgroup G := A.comap e.toMonoidHom
    have hNpre : N ≤ Apre := by
      intro n hn
      exact hNA (Subgroup.mem_map_of_mem e.toMonoidHom hn)
    have hpreK : Apre ≤ K := by
      intro x hx
      have hex : e x ∈ A := hx
      have hexK : e x ∈ K.map e.toMonoidHom := hAK hex
      simpa using (Subgroup.mem_map_equiv.mp hexK)
    have hpreInv : IsConjugateInvariantBy Apre S := by
      intro s a ha
      change e (s * a * s⁻¹) ∈ A
      simpa using hAinv ⟨e s, Subgroup.mem_map_of_mem e.toMonoidHom s.property⟩
        (e a) ha
    rcases h.2.2 Apre hNpre hpreK hpreInv with hpre | hpre
    · left
      have hm := congrArg (Subgroup.map e.toMonoidHom) hpre
      rwa [Subgroup.map_comap_eq_self_of_surjective e.surjective] at hm
    · right
      have hm := congrArg (Subgroup.map e.toMonoidHom) hpre
      rwa [Subgroup.map_comap_eq_self_of_surjective e.surjective] at hm

variable {M : Type u} [Group M]

private def baseMHom (S : Subgroup M) :
    M →* stabilizer S (mVertex S 1) :=
  (embedM S).codRestrict _ (fun m ↦ by
    rw [stabilizer_m_base]
    exact ⟨m, rfl⟩)

private theorem baseMHom_injective (S : Subgroup M) :
    Function.Injective (baseMHom S) := by
  intro x y hxy
  apply embedM_injective S
  exact congrArg Subtype.val hxy

private theorem baseMHom_surjective (S : Subgroup M) :
    Function.Surjective (baseMHom S) := by
  intro y
  have hy : (y : FreeAmalgam S) ∈ Mbar S := by
    rw [← stabilizer_m_base]
    exact y.property
  obtain ⟨m, hm⟩ := hy
  refine ⟨m, Subtype.ext ?_⟩
  exact hm

private noncomputable def baseMEquiv (S : Subgroup M) :
    M ≃* stabilizer S (mVertex S 1) :=
  MulEquiv.ofBijective (baseMHom S)
    ⟨baseMHom_injective S, baseMHom_surjective S⟩

private noncomputable instance finiteBaseStabilizer [Finite M]
    (S : Subgroup M) : Finite (stabilizer S (mVertex S 1)) :=
  Finite.of_equiv M (baseMEquiv S).toEquiv

private theorem base_pCore_map [Finite M] (S : Subgroup M) :
    (pCore 2 M).map (baseMEquiv S).toMonoidHom =
      pCore 2 (stabilizer S (mVertex S 1)) :=
  pCore_map_iso 2 (baseMEquiv S)

private theorem base_twoResidual_map [Finite M] (S : Subgroup M) :
    (twoResidualAmbient (⊤ : Subgroup M)).map
        (baseMEquiv S).toMonoidHom =
      twoResidualAmbient (⊤ : Subgroup (stabilizer S (mVertex S 1))) :=
  twoResidualAmbient_top_map_equiv (baseMEquiv S)

private theorem base_coreResidualCommutator_map [Finite M] (S : Subgroup M) :
    (⁅pCore 2 M, twoResidualAmbient (⊤ : Subgroup M)⁆).map
        (baseMEquiv S).toMonoidHom =
      ⁅pCore 2 (stabilizer S (mVertex S 1)),
        twoResidualAmbient (⊤ : Subgroup (stabilizer S (mVertex S 1)))⁆ := by
  rw [Subgroup.map_commutator, base_pCore_map, base_twoResidual_map]

/-- Transport the distance-two local structure at the distinguished
`M`-vertex back to the original finite group. -/
public theorem base_structure_transport [Finite M] (S : Subgroup M)
    (La : Subgroup (stabilizer S (mVertex S 1)))
    (hElem : IsElementaryAbelian 2
      ↥(⁅pCore 2 (stabilizer S (mVertex S 1)),
        twoResidualAmbient
          (⊤ : Subgroup (stabilizer S (mVertex S 1)))⁆))
    (hIrred : IsIrreducibleSection La ⊥
      ⁅pCore 2 (stabilizer S (mVertex S 1)),
        twoResidualAmbient
          (⊤ : Subgroup (stabilizer S (mVertex S 1)))⁆)
    (hComm :
      ⁅pCore 2 (stabilizer S (mVertex S 1)),
        twoResidualAmbient
          (⊤ : Subgroup (stabilizer S (mVertex S 1)))⁆ ≤
        ⁅⁅pCore 2 (stabilizer S (mVertex S 1)),
            twoResidualAmbient
              (⊤ : Subgroup (stabilizer S (mVertex S 1)))⁆, La⁆) :
    let V := ⁅pCore 2 M, twoResidualAmbient (⊤ : Subgroup M)⁆
    ∃ L : Subgroup M,
      IsElementaryAbelian 2 V ∧
        IsIrreducibleSection L ⊥ V ∧ V ≤ ⁅V, L⁆ := by
  let e := baseMEquiv S
  let VM := ⁅pCore 2 M, twoResidualAmbient (⊤ : Subgroup M)⁆
  let VH := ⁅pCore 2 (stabilizer S (mVertex S 1)),
    twoResidualAmbient (⊤ : Subgroup (stabilizer S (mVertex S 1)))⁆
  let L : Subgroup M := La.map e.symm.toMonoidHom
  have hVforward : VM.map e.toMonoidHom = VH := by
    simpa [VM, VH, e] using base_coreResidualCommutator_map S
  have hVback : VH.map e.symm.toMonoidHom = VM := by
    rw [← hVforward, Subgroup.map_map]
    simp
  have hEback : IsElementaryAbelian 2 (VH.map e.symm.toMonoidHom) := by
    let _ : IsElementaryAbelian 2 VH := hElem
    exact IsElementaryAbelian.map e.symm.toMonoidHom
  have hVMelem : IsElementaryAbelian 2 VM := by
    rwa [hVback] at hEback
  have hIback := isIrreducibleSection_map_equiv e.symm La ⊥ VH hIrred
  have hLIrred : IsIrreducibleSection L ⊥ VM := by
    rw [Subgroup.map_bot, hVback] at hIback
    exact hIback
  have hVMComm : VM ≤ ⁅VM, L⁆ := by
    intro x hx
    have hxmap : x ∈ VH.map e.symm.toMonoidHom := by rwa [hVback]
    obtain ⟨y, hy, hyx⟩ := hxmap
    have hymap : e.symm y ∈ (⁅VH, La⁆).map e.symm.toMonoidHom :=
      Subgroup.mem_map_of_mem e.symm.toMonoidHom (hComm hy)
    rw [Subgroup.map_commutator, hVback] at hymap
    change x ∈ ⁅VM, La.map e.symm.toMonoidHom⁆
    rw [← hyx]
    exact hymap
  exact ⟨L, hVMelem, hLIrred, hVMComm⟩

private theorem vSubgroup_map_equiv
    {G : Type u} {H : Type v} [Group G] [Group H] [Finite G] [Finite H]
    (e : G ≃* H) (S : Sylow 2 G) (T : Sylow 2 H) :
    (SectionTwo.vSubgroup S).map e.toMonoidHom = SectionTwo.vSubgroup T := by
  let Se : Sylow 2 H := S.mapSurjective (f := e.toMonoidHom) e.surjective
  have hsame : SectionTwo.vSubgroup Se = SectionTwo.vSubgroup T := by
    change Subgroup.normalClosure (omegaOneCenterAmbient (Se : Subgroup H) : Set H) =
      Subgroup.normalClosure (omegaOneCenterAmbient (T : Subgroup H) : Set H)
    rw [omegaNormalClosure_eq_sSup_sylows Se, omegaNormalClosure_eq_sSup_sylows T]
  rw [← hsame]
  change (Subgroup.normalClosure (omegaOneCenterAmbient (S : Subgroup G) : Set G)).map
    e.toMonoidHom = Subgroup.normalClosure (omegaOneCenterAmbient (Se : Subgroup H) : Set H)
  rw [Subgroup.map_normalClosure _ e.toMonoidHom e.surjective]
  congr 1
  rw [← Subgroup.coe_map]
  congr 1
  change (omegaOneCenterAmbient (S : Subgroup G)).map e.toMonoidHom =
    omegaOneCenterAmbient ((S : Subgroup G).map e.toMonoidHom)
  exact (omegaOneCenterAmbient_map_injective e.toMonoidHom e.injective _).symm

/-- Transport the canonical action quotient, cardinality, and exact natural
commutator equality at the base vertex to the original group and Sylow. -/
public theorem base_natural_commutator_transport [Finite M]
    (S : Subgroup M) (T : Sylow 2 M)
    (Ta : Sylow 2 (stabilizer S (mVertex S 1)))
    (hA : letI : (SectionTwo.vSubgroup Ta).Normal := Subgroup.normalClosure_normal
      let : (SectionTwo.cSubgroup Ta).Normal := Subgroup.normal_centralizer
      Nonempty (((stabilizer S (mVertex S 1)) ⧸ SectionTwo.cSubgroup Ta) ≃*
        Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)))
    (hcard : Nat.card ↥(⁅pCore 2 (stabilizer S (mVertex S 1)),
      twoResidualAmbient (⊤ : Subgroup (stabilizer S (mVertex S 1)))⁆) = 4)
    (heq : ⁅pCore 2 (stabilizer S (mVertex S 1)),
      twoResidualAmbient (⊤ : Subgroup (stabilizer S (mVertex S 1)))⁆ =
      ⁅SectionTwo.vSubgroup Ta, (⊤ : Subgroup (stabilizer S (mVertex S 1)))⁆) :
    let : (SectionTwo.vSubgroup T).Normal := Subgroup.normalClosure_normal
    let : (SectionTwo.cSubgroup T).Normal := Subgroup.normal_centralizer
    IsSL2Two (M ⧸ SectionTwo.cSubgroup T) ∧
    Nat.card ↥(⁅pCore 2 M, twoResidualAmbient (⊤ : Subgroup M)⁆) = 4 ∧
    ⁅pCore 2 M, twoResidualAmbient (⊤ : Subgroup M)⁆ =
      ⁅SectionTwo.vSubgroup T, (⊤ : Subgroup M)⁆ := by
  let : (SectionTwo.vSubgroup T).Normal := Subgroup.normalClosure_normal
  let : (SectionTwo.cSubgroup T).Normal := Subgroup.normal_centralizer
  let : (SectionTwo.vSubgroup Ta).Normal := Subgroup.normalClosure_normal
  let : (SectionTwo.cSubgroup Ta).Normal := Subgroup.normal_centralizer
  let e := baseMEquiv S
  have hVmap := vSubgroup_map_equiv e T Ta
  have hCmap : (SectionTwo.cSubgroup T).map e.toMonoidHom = SectionTwo.cSubgroup Ta := by
    change (Subgroup.centralizer (SectionTwo.vSubgroup T : Set M)).map e.toMonoidHom =
      Subgroup.centralizer (SectionTwo.vSubgroup Ta : Set _)
    rw [← hVmap]
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      change x ∈ Subgroup.centralizer (SectionTwo.vSubgroup T : Set M) at hx
      rw [Subgroup.mem_centralizer_iff] at hx ⊢
      rintro _ ⟨z, hz, rfl⟩
      simpa only [map_mul] using congrArg e.toMonoidHom (hx z hz)
    · intro hy
      refine ⟨e.symm y, ?_, e.apply_symm_apply y⟩
      change e.symm y ∈ Subgroup.centralizer (SectionTwo.vSubgroup T : Set M)
      rw [Subgroup.mem_centralizer_iff] at hy ⊢
      intro z hz
      apply e.injective
      simpa only [map_mul, e.apply_symm_apply] using hy (e z) ⟨z, hz, rfl⟩
  have hWmap := base_coreResidualCommutator_map S
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨eA⟩ := hA
    exact ⟨(QuotientGroup.congr _ _ e hCmap).trans eA⟩
  · rw [← hWmap, Subgroup.card_map_of_injective (f := e.toMonoidHom) e.injective] at hcard
    exact hcard
  · apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
    rw [hWmap, Subgroup.map_commutator, hVmap, Subgroup.map_top_of_surjective e.toMonoidHom e.surjective]
    exact heq

end Stellmacher.PushingUp
