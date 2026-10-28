module

public import Theory.GroupTheory.CComponent.FixedOrbitSelection
public import Theory.GroupTheory.CComponent.FixedOrbitClosure
public import Theory.GroupTheory.ComponentLocalOrbitCore
public import Theory.GroupAction.PrimeGroupFixedImage
public import CFSG.Quasithin.ChapterI.Section03.OrdinaryBalance
public import CFSG.Quasithin.ChapterI.Section03.SylowAutomorphisms

/-!
# Arbitrary two-subgroup component orbits

The genuine GLS II 5.17 bound places a fixed two-component in the source
two-layer; the finite-section S₂ hypothesis is discharged by
`SylowAutomorphisms.hasTwoSchreier`. Quotienting by the literal odd core
preserves the centralizer's C-components and identifies the ambient two-layer
with the ordinary component layer. The fixed central-product argument selects
one actor orbit, and perfectness lifts containment through the odd kernel.

The invariant-seed normal-generation theorem then supplies both normal closures
and both subnormal closures. Restriction supplies the component of the literal
intersection with the original centralizer. This proves the internal-actor
clauses (i)-(iii) of GLS II, Chapter B, Proposition 5.22, including the
odd-E closure used in Aschbacher--Smith I.3. The universal 5.17 premise remains
explicit for its separate producer; no B₂ or model hypothesis is used.
The full external-action statement, including clause (iv), is assembled in
`GeneralTwoOrbit.Actions`; its quotient branch is in `GeneralTwoOrbit.Quotient`.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterI.GeneralTwoOrbit
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The genuine internal source bound, with S₂ discharged. -/
theorem seed_le_twoLayer (balance : OrdinaryBalance.TwoLayerCentralizerBalance.{u})
    (P : Subgroup G) (hP : IsPGroup 2 P)
    (I : Subgroup (centralizer (P : Set G))) (hI : I.IsTwoComponent) :
    I.map (centralizer (P : Set G)).subtype ≤ twoComponentLayer G :=
  (map_mono hI.le_twoComponentLayer).trans
    (balance G (SylowAutomorphisms.hasTwoSchreier G) P hP)

/-- Orbit selection from the literal layer bound; no B₂ hypothesis is used. -/
theorem exists_twoComponent_orbit_of_layer_bound
    (P : Subgroup G) (hP : IsPGroup 2 P)
    (I : Subgroup (centralizer (P : Set G))) (hI : I.IsTwoComponent)
    (hb : I.map (centralizer (P : Set G)).subtype ≤ twoComponentLayer G) :
    ∃ J : Subgroup G, J.IsTwoComponent ∧
      I.map (centralizer (P : Set G)).subtype ≤ componentOrbit J P := by
  let O := pPrimeCore 2 G
  let q := QuotientGroup.mk' O
  let C := centralizer (P : Set G)
  let Cbar := centralizer (P.map q : Set (G ⧸ O))
  let D := I.map C.subtype
  have hO : Odd (Nat.card O) := Nat.coprime_two_left.mp pPrimeCore_coprime_card
  have hC : C.map q = Cbar := centralizer_map_of_prime_free_kernel q
    (QuotientGroup.mk'_surjective O)
    (by simpa only [q, QuotientGroup.ker_mk'] using hO.not_two_dvd_nat) P hP
  let f : C →* Cbar := (q.comp C.subtype).codRestrict Cbar (fun x =>
    hC ▸ mem_map_of_mem q x.property)
  have hf : Function.Surjective f := by
    intro y
    have hy : (y : G ⧸ O) ∈ C.map q := hC.symm ▸ y.property
    obtain ⟨x, hx, he⟩ := hy
    exact ⟨⟨x, hx⟩, Subtype.ext he⟩
  have hk : Odd (Nat.card f.ker) := by
    have he : f.ker = O.comap C.subtype := by
      dsimp only [f]
      rw [MonoidHom.ker_codRestrict, ← MonoidHom.comap_ker, QuotientGroup.ker_mk']
    rw [he]
    exact Nat.coprime_two_left.mp (hO.coprime_two_left.of_dvd_right
      (O.card_comap_dvd_of_injective C.subtype C.subtype_injective))
  let : Group.IsSolvable f.ker := odd_order_theorem _ hk
  have hfI : (I.map f).IsCComponent := cComponent_map_of_solvable_ker hI.1 f hf
  have hid : (I.map f).map Cbar.subtype = D.map q := by
    rw [map_map, map_map]
    rfl
  have hDC : D.map q ≤ Cbar := hC ▸ map_mono (map_subtype_le I)
  have hDI : ((D.map q).subgroupOf Cbar).IsCComponent := by
    rw [← hid]
    simpa only [subgroupOf, comap_map_eq_self_of_injective Cbar.subtype_injective] using hfI
  have hbar : D.map q ≤ componentLayer (G ⧸ O) :=
    (map_mono hb).trans_eq Balance.map_twoComponentLayer_oddCore
  obtain ⟨Jbar, hJbar, hDbar⟩ := hDI.le_componentOrbit_of_le_componentLayer
    (P.map q) hDC hbar
  obtain ⟨J, ⟨hJ, hJq⟩, _⟩ := Balance.existsUnique_twoComponent_of_oddCore_component hJbar
  refine ⟨J, hJ, ?_⟩
  let X := componentOrbit J P
  have hDX : D.map q ≤ X.map q := by
    rw [map_componentOrbit, hJq]
    exact hDbar
  have hDO : D ≤ X ⊔ O := by
    simpa only [q, comap_map_eq, QuotientGroup.ker_mk'] using map_le_iff_le_comap.mp hDX
  let := hI.1.perfect
  let : Group.IsPerfect D := Group.IsPerfect.map C.subtype
  let := hJ.1.perfect
  let : Group.IsPerfect X := isPerfect_iSup_conjugates J P
  let : Group.IsSolvable O := odd_order_theorem _ hO
  have hres := le_map_solvableResidual_of_isPerfect D (X ⊔ O) hDO
  rwa [hJ.1.orbit_subnormal.solvableResidual_sup_eq O le_normalizer_of_normal] at hres

omit [Finite G] in
private theorem orbit_mono_actor (D A B : Subgroup G) (hAB : A ≤ B) :
    componentOrbit D A ≤ componentOrbit D B :=
  iSup_le fun a => le_iSup (fun b : B => D.map (MulAut.conj (b : G)).toMonoidHom)
    ⟨a, hAB a.property⟩

/-- The selected orbit is normal in the source two-layer. -/
theorem twoLayer_le_normalizer_orbit {J : Subgroup G} (hJ : J.IsTwoComponent)
    (P : Subgroup G) : twoComponentLayer G ≤ normalizer (componentOrbit J P : Set G) := by
  have hLC : twoComponentLayer G ≤ cComponentLayer G :=
    sSup_le fun K hK => le_cComponentLayer hK.1
  exact hLC.trans ((le_iInf fun p : P => cComponentLayer_le_normalizer
    (hJ.1.map_equiv (MulAut.conj (p : G)))).trans
      (iInf_normalizer_le_normalizer_iSup _))

omit [Finite G] in
/-- Every selected orbit lies in the literal source two-layer. -/
theorem orbit_le_twoLayer {J : Subgroup G} (hJ : J.IsTwoComponent) (P : Subgroup G) :
    componentOrbit J P ≤ twoComponentLayer G :=
  iSup_le fun p => (hJ.map_equiv (MulAut.conj (p : G))).le_twoComponentLayer

/-- GLS 5.22(ii): a selected orbit is both relative normal closures and
both subnormal closures. The additional odd-E equality is used by I.3. -/
theorem selected_orbit_closures
    (P : Subgroup G) (I : Subgroup (centralizer (P : Set G)))
    (hI : I.IsTwoComponent) {J : Subgroup G} (hJ : J.IsTwoComponent)
    (hIJ : I.map (centralizer (P : Set G)).subtype ≤ componentOrbit J P) :
    let D := I.map (centralizer (P : Set G)).subtype
    let X := componentOrbit J P
    componentOrbit D X = X ∧
    componentOrbit D (twoComponentLayer G) = X ∧
    componentOrbit D (oddELayer G) = X ∧
    IsLeast {M : Subgroup G | D ≤ M ∧ M.IsSubnormal} X ∧
    IsLeast {M : Subgroup G | D ≤ M ∧ M ≤ twoComponentLayer G ∧
      (M.subgroupOf (twoComponentLayer G)).IsSubnormal} X := by
  let C := centralizer (P : Set G)
  let D := I.map C.subtype
  let X := componentOrbit J P
  have hDC : D ≤ C := map_subtype_le I
  have hAI : P ≤ normalizer (D : Set G) :=
    (le_centralizer_iff.mp hDC).trans (Subgroup.centralizer_le_normalizer _)
  let := hI.1.perfect
  let : Group.IsPerfect D := Group.IsPerfect.map C.subtype
  have hDne : D ≠ ⊥ := fun he => hI.1.ne_bot
    ((map_eq_bot_iff_of_injective I C.subtype_injective).mp he)
  have hgen : componentOrbit D X = X := hJ.1.invariant_seed_normalClosure hDne hIJ hAI
  have hXL : X ≤ twoComponentLayer G := orbit_le_twoLayer hJ P
  have hLnorm : twoComponentLayer G ≤ normalizer (X : Set G) :=
    twoLayer_le_normalizer_orbit hJ P
  have hsub : X.IsSubnormal := hJ.1.orbit_subnormal
  have hmin (M : Subgroup G) (hDM : D ≤ M) (hM : M.IsSubnormal) : X ≤ M :=
    le_subnormal_of_self_normalClosure hgen hM hDM
  have hgenL : componentOrbit D (twoComponentLayer G) = X := by
    apply le_antisymm (iSup_conjugates_le_of_le_normalizer _ _ _ hIJ hLnorm)
    exact hgen.ge.trans (orbit_mono_actor D X _ hXL)
  have hgenO : componentOrbit D (oddELayer G) = X := by
    let := hJ.1.perfect
    let : Group.IsPerfect X := isPerfect_iSup_conjugates J P
    let : Group.IsSolvable (pPrimeCore 2 G) := odd_order_theorem _
      (Nat.coprime_two_left.mp pPrimeCore_coprime_card)
    have ho : pPrimeCore 2 G ≤ normalizer (X : Set G) :=
      le_normalizer_iff_commutator_le_left.mpr
        (hsub.commutator_le_of_solvable _ le_normalizer_of_normal)
    apply le_antisymm
      (iSup_conjugates_le_of_le_normalizer _ _ _ hIJ (sup_le ho hLnorm))
    exact hgenL.ge.trans (orbit_mono_actor D _ _ le_sup_right)
  refine ⟨hgen, hgenL, hgenO, ⟨⟨hIJ, hsub⟩, fun M hM => hmin M hM.1 hM.2⟩,
    ⟨⟨hIJ, hXL, hsub.subgroupOf⟩, ?_⟩⟩
  intro M hM
  exact hmin M hM.1 (hM.2.2.trans hM.2.1
    (inferInstance : (twoComponentLayer G).Normal).isSubnormal)

omit [Finite G] in
/-- GLS 5.22(iii), with the seed and the fixed subgroup embedded literally. -/
theorem selected_orbit_fixed_component
    (P : Subgroup G) (I : Subgroup (centralizer (P : Set G)))
    (hI : I.IsTwoComponent) {J : Subgroup G}
    (hIJ : I.map (centralizer (P : Set G)).subtype ≤ componentOrbit J P) :
    ((I.map (centralizer (P : Set G)).subtype).subgroupOf
      (componentOrbit J P ⊓ centralizer (P : Set G))).IsTwoComponent := by
  let C := centralizer (P : Set G)
  let D := I.map C.subtype
  let M := componentOrbit J P ⊓ C
  have hDC : D ≤ C := map_subtype_le I
  have hDM : D ≤ M := le_inf hIJ hDC
  have hD : (D.subgroupOf C).IsTwoComponent := by
    simpa only [D, subgroupOf, comap_map_eq_self_of_injective C.subtype_injective] using hI
  let e := (subgroupOfEquivOfLe hDC).trans (subgroupOfEquivOfLe hDM).symm
  let := hD.2
  exact ⟨hD.1.subgroupOf_of_le hDM inf_le_right,
    IsQuasisimple.of_mulEquiv (QuotientGroup.congr _ _ e (pPrimeCore_map_iso 2 e))⟩

/-- All internal orbit and closure clauses of GLS 5.22(i)-(iii), conditional
only on the genuine universal GLS 5.17 input. -/
theorem exists_orbit_and_closures
    (balance : OrdinaryBalance.TwoLayerCentralizerBalance.{u})
    (P : Subgroup G) (hP : IsPGroup 2 P)
    (I : Subgroup (centralizer (P : Set G))) (hI : I.IsTwoComponent) :
    ∃ J : Subgroup G, J.IsTwoComponent ∧
      let D := I.map (centralizer (P : Set G)).subtype
      let X := componentOrbit J P
      D ≤ X ∧
      componentOrbit D X = X ∧
      componentOrbit D (twoComponentLayer G) = X ∧
      componentOrbit D (oddELayer G) = X ∧
      IsLeast {M : Subgroup G | D ≤ M ∧ M.IsSubnormal} X ∧
      IsLeast {M : Subgroup G | D ≤ M ∧ M ≤ twoComponentLayer G ∧
        (M.subgroupOf (twoComponentLayer G)).IsSubnormal} X ∧
      (D.subgroupOf (X ⊓ centralizer (P : Set G))).IsTwoComponent := by
  obtain ⟨J, hJ, hIJ⟩ := exists_twoComponent_orbit_of_layer_bound P hP I hI
    (seed_le_twoLayer balance P hP I hI)
  obtain ⟨hself, hlayer, hodd, hmin, hminlayer⟩ := selected_orbit_closures P I hI hJ hIJ
  exact ⟨J, hJ, hIJ, hself, hlayer, hodd, hmin, hminlayer,
    selected_orbit_fixed_component P I hI hIJ⟩

end CFSG.Quasithin.ChapterI.GeneralTwoOrbit
