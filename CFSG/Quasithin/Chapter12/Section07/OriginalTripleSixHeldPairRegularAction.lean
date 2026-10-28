module

public import CFSG.Quasithin.Chapter12.Section07.OriginalTripleSixHeldPairFourImages
public import Theory.SpecificGroups.SymmetricEight.SingularDisplacement
public import Theory.SpecificGroups.SymmetricEight.RegularDihedralPair.FixedPointFreeCorrected
public import Theory.SpecificGroups.DihedralEightElementaryCoverage

/-! The actual square action of the original dihedral quotient is regular. -/
public noncomputable section
open Subgroup Theory.GroupTheory Representation Atlas.Codes
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section07
open Section02 ChapterB.QuasisimpleSource
variable {G : Type*} [Group G]

private theorem normalizer_dihedral_factor (T Y : Subgroup G) (hTY : T≤Y)
    (π : T→*DihedralGroup 4) (hπ : Function.Surjective π)
    (f : Y→*Equiv.Perm (Fin 8))
    (hk : f.ker=(π.ker.map T.subtype).subgroupOf Y) :
    ∃ d : DihedralGroup 4→*Equiv.Perm (Fin 8), Function.Injective d ∧
      ∀ t : T, d (π t)=f (inclusion hTY t) := by
  let fT := f.comp (inclusion hTY)
  have hker : fT.ker=π.ker := by
    ext x
    change f (inclusion hTY x)=1 ↔ x∈π.ker
    rw [←f.mem_ker,hk]
    change x.val∈π.ker.map T.subtype ↔ x∈π.ker
    constructor
    · rintro ⟨y,hy,he⟩
      exact (show y=x from Subtype.ext he) ▸ hy
    · intro hx
      exact ⟨x,hx,rfl⟩
  let d := π.liftOfSurjective hπ ⟨fT,hker.ge⟩
  have hd (t : T) : d (π t)=fT t :=
    MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ _
  refine ⟨d,?_,hd⟩
  apply (injective_iff_map_eq_one d).mpr
  intro x hx
  obtain ⟨t,rfl⟩ := hπ x
  have hft : t∈fT.ker := (hd t).symm.trans hx
  have hpt : t∈π.ker := hker ▸ hft
  exact π.mem_ker.mp hpt

variable [Finite G] {T : Sylow 2 G} {K U : Subgroup G}

theorem original_tripleSix_escaping_pair_regular_action
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T K)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T K U)
    (a : ActionEquiv D.quotientAction Hexacode.evenAction) (t : U) (ht : t≠1)
    (heven : 2∣(centralizer ({(t:G)} : Set G)).relIndex K)
    (hout : ¬centralizer ({(t:G)} : Set G)≤normalizer (K : Set G)) :
    ∃ π : T→*DihedralGroup 4, Function.Surjective π ∧
      let P := π.ker.map (T : Subgroup G).subtype
      let Y := normalizer (P : Set G)
      P≤(T : Subgroup G) ∧ ∃ hTY : (T : Subgroup G)≤Y, Nat.card P=128 ∧ ∃ hEx : IsExtraspecial 2 P, letI := hEx
      
      Nonempty (P≃*DihedralCentralProductThree.Model) ∧
      Nat.card (U⊓P : Subgroup G)=16 ∧ Nat.card ((U.subgroupOf T).map π)=4 ∧
      ∃ z : G, orderOf z=2 ∧ z∈U ∧
        centerIn P=zpowers z ∧ centerIn (T : Subgroup G)=zpowers z ∧
        centralizer (P : Set G)=zpowers z ∧ Y≤centralizer ({z} : Set G) ∧
        normalizer (K : Set G)⊓centralizer ({z} : Set G)≤Y ∧
        let H := centralizer ({(t:G)} : Set G)
        let Lt := (pResidual 2 (K⊓H : Subgroup G)).map (K⊓H).subtype
        let B := conjugateSpanBy Lt H
        ∃ k∈K, ∃ S : Sylow 2 B, ∃ W : Subgroup G,
          ∃ hWe : IsElementaryAbelian 2 W, letI := hWe
          let R := ((S : Subgroup B).map B.subtype).map (MulAut.conj k).toMonoidHom
          let I := normalizer (W : Set G)
          U≤R ∧ W≤R ∧ R≤(T : Subgroup G) ∧ U⊔W=R ∧
          Nat.card W=64 ∧ (T : Subgroup G)≤normalizer (R : Set G)⊓I ∧
          centralizer (W : Set G)=W ∧ I.pCoreIn 2=W ∧
          Nat.card (W⊓P : Subgroup G)=16 ∧ centerIn P≤W ∧
          (U⊓P : Subgroup G)≠W⊓P ∧
          let Q := I⊓centralizer ({z} : Set G)
          Q≤Y ∧
            (∃ q : Q→*Equiv.Perm (Fin 4), Function.Surjective q ∧ q.ker=P.subgroupOf Q) ∧
            let Q₀ := normalizer (K : Set G)⊓centralizer ({z} : Set G)
            (∃ q₀ : Q₀→*Equiv.Perm (Fin 4), Function.Surjective q₀ ∧ q₀.ker=P.subgroupOf Q₀) ∧
            Q₀≠Q ∧ Q₀⊓Q=(T : Subgroup G) ∧ Q₀.pCoreIn 2≠Q.pCoreIn 2 ∧
            let J := Q₀⊔Q
            J≤Y ∧ ChapterF.IsGoldschmidtTriple (Q₀.subgroupOf J) (Q.subgroupOf J) ∧
              (Q₀.subgroupOf J).pCoreIn 2≠(Q.subgroupOf J).pCoreIn 2 ∧ J.pCoreIn 2=P ∧
              Q₀.pCoreIn 2=P⊔U ∧ Q.pCoreIn 2=P⊔W ∧
              Nat.card ((W.subgroupOf T).map π)=4 ∧
              (U.subgroupOf T).map π≠(W.subgroupOf T).map π ∧
              ∃ e : (ExtraspecialSquare.form P).IsometryEquiv
                (ClassicalOrthogonal.formD 3 (ZMod 2)),
                ∃ f : Y→*Equiv.Perm (Fin 8), f.ker=P.subgroupOf Y ∧
                  (∀ (y : Y) (v : P⧸center P),
                    (ClassicalOrthogonal.BinaryD3Comparison.symmetricEquiv (f y)).val
                      (e (Additive.ofMul v))=
                        e (Additive.ofMul (quotientAut (center P) (P.normalizerMonoidHom y) v))) ∧
                  (∀ y : Y, y.val∈U ∨ y.val∈W →
                    ∀ v, ClassicalOrthogonal.formD 3 (ZMod 2)
                      ((ClassicalOrthogonal.BinaryD3Comparison.symmetricEquiv (f y)).val v-v)=0) ∧
                  ∃ d : DihedralGroup 4→*Equiv.Perm (Fin 8), Function.Injective d ∧
                    (∀ t : T, d (π t)=f (inclusion hTY t)) ∧
                    ∀ x : DihedralGroup 4, x≠1 → ∀ i, d x i≠i := by
  obtain ⟨π,hπ,hPT,hTY,hPc,hEx,hmodel,hUP,hUimage,z,hz,hzU,hZP,hZT,hCP,hYC,hMY,
    k,hk,S,W,hWe,hUR,hWR,hRT,hgen,hWc,hTN,hCW,hcore,hWP,hZW,hneq,hQY,
    ⟨q,hq,hqker⟩,⟨q₀,hq₀,hq₀ker⟩,hne,hint,hcorene,hJY,htriple,hcoreJne,hJP,
    hcore₀,hcore₁,hWimage,himages,e,f,hfk,hfe,hsing⟩ :=
    original_tripleSix_escaping_pair_four_images h structural D a t ht heven hout
  let P := π.ker.map (T : Subgroup G).subtype
  let Y := normalizer (P : Set G)
  let := hEx
  let := D.elementary
  let := hWe
  let A := (U.subgroupOf T).map π
  let B := (W.subgroupOf T).map π
  let : IsElementaryAbelian 2 (U.subgroupOf T) := IsElementaryAbelian.subgroupOf D.le_sylow
  let : IsElementaryAbelian 2 (W.subgroupOf T) := IsElementaryAbelian.subgroupOf (hWR.trans hRT)
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.map π
  let : IsElementaryAbelian 2 B := IsElementaryAbelian.map π
  obtain ⟨d,hd,hdf⟩ := normalizer_dihedral_factor (T : Subgroup G) Y hTY π hπ f hfk
  have hfree : ∀ x : DihedralGroup 4, x≠1 → ∀ i, d x i≠i := by
    apply ClassicalOrthogonal.BinaryD3Comparison.dihedral_fixedPointFree_of_two_involution_planes_nontrivial d A B
    · intro x
      rcases Theory.SpecificGroups.DihedralEight.orderOf_cases x with hh|hh|hh
      · exact Or.inl (orderOf_eq_one_iff.mp hh)
      · exact Or.inr (Or.inl hh)
      · exact Or.inr (Or.inr hh)
    · exact Theory.SpecificGroups.DihedralEight.involution_mem_of_distinct_elementary_four A B hUimage hWimage himages
    · intro x hx hm
      have hdx : d x≠1 := fun he => hx (hd (he.trans d.map_one.symm))
      apply ClassicalOrthogonal.BinaryD3Comparison.fixedPointFree_of_singular_displacement (d x) hdx
      rcases hm with hm|hm
      · obtain ⟨u,hu,rfl⟩ := hm
        rw [hdf]
        exact hsing (inclusion hTY u) (Or.inl hu)
      · obtain ⟨w,hw,rfl⟩ := hm
        rw [hdf]
        exact hsing (inclusion hTY w) (Or.inr hw)
  exact ⟨π,hπ,hPT,hTY,hPc,hEx,hmodel,hUP,hUimage,z,hz,hzU,hZP,hZT,hCP,hYC,hMY,
    k,hk,S,W,hWe,hUR,hWR,hRT,hgen,hWc,hTN,hCW,hcore,hWP,hZW,hneq,hQY,
    ⟨q,hq,hqker⟩,⟨q₀,hq₀,hq₀ker⟩,hne,hint,hcorene,hJY,htriple,hcoreJne,hJP,
    hcore₀,hcore₁,hWimage,himages,e,f,hfk,hfe,hsing,d,hd,hdf,hfree⟩

end CFSG.Quasithin.Chapter12.Section07
