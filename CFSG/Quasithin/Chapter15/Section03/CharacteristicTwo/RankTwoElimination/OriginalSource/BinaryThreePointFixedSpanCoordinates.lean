module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource.BinaryThreePointFourFixedCover
public import Theory.Representation.BinaryEndpointInduction.FixedCosetLift
public import Theory.Representation.BinaryFifteenPoint.InvariantLattice

/-!
# Literal coordinates for the original fixed-four-span quotient

The actual endpoint marking sends the original B to the frozen endpoint
parabolic. The original H/<z> seed therefore gives an onto map from the
literal fifteen-coordinate permutation module to the same U/<z>. Both the
point-quotient conjugation action and the exact inverse left actors remain
in the conclusion, so the finite invariant-lattice certificate applies to
this kernel without changing the source module.
-/
public noncomputable section
open Subgroup Theory.GroupTheory Representation Matrix
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
open LinearThree LinearThree.OriginalSource CoreActions ChapterC BinaryMS.MS93
open CFSG.Quasithin.Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
open BinaryEndpointInduction
variable {G : Type*} [Group G] [Finite G]

/-- The actual fixed-line quotient is covered by the same fifteen matrices
whose invariant lattice is certified in BinaryFifteenPoint. -/
theorem binary_three_source_fixed_span_coordinates
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (d : LocalData G)
    (hempty : MainForward.faithfulLocalComponents d.T = ∅)
    (hM : ChapterA.Section05To06.IsOrderingMaximal d.T d.M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions d.T : Set G)) = {d.Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (d.T : Subgroup G)).ncard)
    {I : Subgroup G} (hI : I ∈ d.Hplus) (htwo : OutsideStructure.RankTwoCase d I)
    (hf : HasCharacteristicTwo I) (c : ComponentWitness d I)
    (e : (c.L ⧸ pCore 2 c.L) ≃* PSL(3,ZMod 2))
    (b : BinaryMS.Input KnownSimple.IsKnownSimple
      (c.L.subgroupOf (c.L ⊔ d.S)) (d.S.subgroupOf (c.L ⊔ d.S)))
    (t : InputSetup b)
    (hc : ¬ IsMulCommutative (BinaryMS.commutatorCore (c.L.subgroupOf (c.L ⊔ d.S))))
    (hb : 4 < t.geometry.b t.reduction.radical)
    (z : G) (hzH : z ∈ LinearThree.OriginalSource.intrinsicFour c.L)
    (hz2 : orderOf z = 2) (hLS : c.L ⊔ d.S ≤ centralizer ({z} : Set G))
    (P : Sylow 2 (centralizer ({z} : Set G)))
    (hP : (P : Subgroup _).map (centralizer ({z} : Set G)).subtype = d.S)
    (K : Subgroup ((centralizer ({z} : Set G)) ⧸ pCore 2 (centralizer ({z} : Set G))))
    [K.Normal]
    (hBK : (c.L.subgroupOf (centralizer ({z} : Set G))).map
      (QuotientGroup.mk' (pCore 2 (centralizer ({z} : Set G)))) ≤ K)
    (hm : ClassicalGroup.IsPSL K 4 2) :
    let C := centralizer ({z} : Set G)
    let q := QuotientGroup.mk' (pCore 2 C)
    let B := (c.L.subgroupOf C).map q
    let H := intrinsicFour c.L
    let Z := zpowers z
    let U := conjugateSpanBy H C
    ∃ hZ : (Z.subgroupOf U).Normal,
      let := hZ
      ∃ hel : IsElementaryAbelian 2 (U ⧸ Z.subgroupOf U),
        let := hel
        ∃ ρ : (C ⧸ pCore 2 C) →* MulAut (U ⧸ Z.subgroupOf U),
          (∀ (x : C) (u v : U), (v : G)=x*(u : G)*(x : G)⁻¹ →
            ρ (q x) (QuotientGroup.mk' (Z.subgroupOf U) u)=
              QuotientGroup.mk' (Z.subgroupOf U) v) ∧
          ∃ h : H,
            let w := Additive.ofMul (QuotientGroup.mk' (Z.subgroupOf U)
              (inclusion (le_conjugateSpanBy H C) h))
            let τ := elementaryRepresentation (p := 2) (ρ.comp K.subtype)
            w ≠ 0 ∧ (∀ b : B.subgroupOf K, τ b.val w=w) ∧
            Submodule.span (ZMod 2) (Set.range (fun k : K => τ k w))=⊤ ∧
            ∀ eK : K ≃* SL(4,ZMod 2),
              (B.subgroupOf K).map eK.toMonoidHom=endpointParabolic →
              ∃ F : (Fin 15 → ZMod 2) →ₗ[ZMod 2] Additive (U ⧸ Z.subgroupOf U),
                Function.Surjective F ∧
                (∀ i : Fin 15, F (Pi.single i 1)=τ (eK.symm (cosetRepresentative i)⁻¹) w) ∧
                (∀ (a : Fin 6) (x : Fin 15 → ZMod 2),
                  F (x ᵥ* BinaryFifteenPoint.permutationActor a)=
                    τ (eK.symm (cosetActor a)⁻¹) (F x)) ∧
                ∃ r : Fin 8, F.ker=BinaryFifteenPoint.invariantSubspace r ∧
                  Module.finrank (ZMod 2) (Additive (U ⧸ Z.subgroupOf U)) +
                    BinaryFifteenPoint.rowDimension r=15 := by
  let C := centralizer ({z} : Set G)
  let q := QuotientGroup.mk' (pCore 2 C)
  let B := (c.L.subgroupOf C).map q
  let H := intrinsicFour c.L
  let Z := zpowers z
  let U := conjugateSpanBy H C
  obtain ⟨_,_,_,_,_,_,_,hZ,hel,ρ,hρ,h,hw,_,hfix,hspan,_⟩ :=
    binary_three_source_four_fixed_cover
      hG d hempty hM hu hmany hI htwo hf c e b t hc hb z hzH hz2 hLS P hP K hBK hm
  let := hZ
  let := hel
  let w := Additive.ofMul (QuotientGroup.mk' (Z.subgroupOf U)
    (inclusion (le_conjugateSpanBy H C) h))
  let τ := elementaryRepresentation (p := 2) (ρ.comp K.subtype)
  refine ⟨hZ,hel,ρ,hρ,h,hw,hfix,hspan,?_⟩
  intro eK heK
  let τ' := τ.comp eK.symm.toMonoidHom
  have hfix' (p : endpointParabolic) : τ' p.val w=w := by
    have hp : p.val ∈ (B.subgroupOf K).map eK.toMonoidHom := heK.symm ▸ p.property
    have hb : eK.symm p.val ∈ B.subgroupOf K := (mem_map_equiv).mp hp
    exact hfix ⟨eK.symm p.val,hb⟩
  have hspan' : Submodule.span (ZMod 2) (Set.range (fun g : SL(4,ZMod 2) => τ' g w))=⊤ := by
    apply top_unique
    rw [←hspan]
    apply Submodule.span_le.mpr
    rintro _ ⟨k,rfl⟩
    apply Submodule.subset_span
    refine ⟨eK k,?_⟩
    change τ (eK.symm (eK k)) w=τ k w
    rw [eK.symm_apply_apply]
  obtain ⟨F,hF,hFi,hFa⟩ := exists_fixed_coset_cover
    BinaryFifteenPoint.permutationActor BinaryFifteenPoint.permutationActor_entry
    τ' w hfix' hspan'
  obtain ⟨r,hr⟩ := BinaryFifteenPoint.quotient_kernel F (by
    intro k x hx
    change F (x ᵥ* BinaryFifteenPoint.permutationActor ⟨k.val,by omega⟩)=0
    rw [hFa,LinearMap.mem_ker.mp hx,map_zero])
  have hd := F.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hF,_root_.finrank_top,hr,
    BinaryFifteenPoint.invariantSubspace_finrank] at hd
  have hd' : Module.finrank (ZMod 2) (Additive (U ⧸ Z.subgroupOf U)) +
      BinaryFifteenPoint.rowDimension r=15 := by
    simpa only [Module.finrank_pi,Fintype.card_fin] using hd
  exact ⟨F,hF,hFi,hFa,r,hr,hd'⟩

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
