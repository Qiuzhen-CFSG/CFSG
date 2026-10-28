module
public import Glauberman.PushingUpSL2DegreeNaturalLayers
public import Glauberman.PushingUpSL2DegreeMarkedPair
public import Theory.GroupTheory.QuotientIntersection
public import Theory.GroupTheory.SubgroupTransport.GapTriple
public import Theory.GroupTheory.SubgroupTransport.GapPowerTwist
public import Theory.GroupTheory.ClassThreeInvariantQuotient
public import Theory.GroupTheory.PCoreFrattiniTransport
public import Theory.GroupTheory.SubgroupTransport.TwistedQuotient

/-!
# Original-degree nonabelian reduction with its exact parameter

The first-gap action kernel constructs a terminal triple commutator.
Point covering makes it escape its predecessor. The exact gap identity
v = 2w, k = 5w then supplies the error bounds for the power twist alpha^w.
The marked commutator survives its largest invariant normal kernel, and
its two-step escape survives the literal quotient map. The quotient thus
retains class three and has intersection-diagram parameter exactly two.

The entire removed kernel has central chief factors and is centralized by
the original two-residual. The original SL₂ marking descends compatibly,
without changing the field or removing central attachments.

Source: Niles, *Pushing-up in finite groups* (1979), Lemmas 6.4--6.6,
pp.53--55. Used for the same F₀ witness in
`NonbinarySymplectic.CriticalReduction.RootProductNilesReduction`.
The characteristic-two class-three exclusion and original commutator
conclusion remain necessary for the later root-product contradiction.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Theory.GroupTheory.SubgroupTransport NilesRankOneKernel
open scoped MatrixGroups IsMulCommutative
namespace Glauberman
variable {G F : Type*} [Group G] [Finite G] [Field F] [Finite F] [CharP F 2]

@[expose] def NilesTerminalTriple (S : Subgroup G) (α : MulAut S) : Prop :=
  ∃ g : G, g ∈ pResidual 2 G ∧ S ⊔ S.map (MulAut.conj g).toMonoidHom = ⊤ ∧
    S ⊓ S.map (MulAut.conj g).toMonoidHom = pCore 2 G ∧ ∃ w : ℕ, 0 < w ∧ ∃ Z : Subgroup G,
    Z ≤ omegaCenterIn (pCore 2 G) ∧
    Z ≤ (S.map (MulAut.conj g).toMonoidHom).lowerCentralSeries 2 ∧
    ¬ (image (twistedConjugacy S (α^w) g))^[2] Z ≤ pCore 2 G

/-- The original-degree exact diagram constructs the terminal triple
commutator and its half-period escape, unless the Sylow already has class two. -/
theorem original_sl2_terminal_triple
    (e : (G ⧸ pCore 2 G) ≃* SL(2,F)) {n : ℕ}
    (hn : 1 < n) (hF : Nat.card F = 2^n)
    (S : Sylow 2 G) (α : MulAut S)
    (hfit : generalizedFitting G = pCore 2 G)
    (hno : NoInvariantNormal (S : Subgroup G) α) :
    (S : Subgroup G).lowerCentralSeries 2 = ⊥ ∨ NilesTerminalTriple (S : Subgroup G) α := by
  obtain ⟨g,hg,hgen,hinter,hnum,v,hv,hj,hshort,hzs,hzt,hzq,hzg,htwice,hpoint,hVn,hbranch⟩ :=
    original_sl2_exact_layers e hn hF S α hfit hno
  let T := (S : Subgroup G).map (MulAut.conj g).toMonoidHom
  let φ := twistedConjugacy (S : Subgroup G) α g
  let X := intervalDiagram φ (3*v)
  rcases hbranch with hc | ⟨k,hk,hkw,hparam,heven,hex,hgap,hN,hM,hVN,hNM,hMQ,hNV,hQM,hMQZ,hd,hidx,hEq,hEn,hEm,hkernel⟩
  · apply Or.inl
    have htwo : T.lowerCentralSeries 2 = ⊥ := by
      simp only [Subgroup.lowerCentralSeries_succ,Subgroup.lowerCentralSeries_zero]
      exact commutator_eq_bot_iff_le_centralizer.mpr (hc.1.trans inf_le_right)
    apply map_injective (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).injective
    rw [Subgroup.map_lowerCentralSeries,Subgroup.map_bot]
    exact htwo
  · apply Or.inr
    have hneS : ¬ (S : Subgroup G) ≤ T := by
      intro hh
      have hi := hnum.index_left
      have he : ((S : Subgroup G) ⊓ T).relIndex (S : Subgroup G) = 1 :=
        relIndex_eq_one.mpr (le_inf le_rfl hh)
      rw [he] at hi
      have := hnum.nontrivial_index
      omega
    have hneT : ¬ T ≤ (S : Subgroup G) := by
      intro hh
      have hi := hnum.index_right
      have he : ((S : Subgroup G) ⊓ T).relIndex T = 1 :=
        relIndex_eq_one.mpr (le_inf hh le_rfl)
      rw [he] at hi
      have := hnum.nontrivial_index
      omega
    have hgenR : ∀ a b : ℕ, a+b < 3*v →
        intervalCell φ.symm a (b+1) ⊔ intervalCell φ.symm (a+1) b = intervalCell φ.symm a b := by
      intro a b hab
      simpa only [intervalCell_symm,sup_comm] using hj b a (by omega)
    have hgapR := intervalDiagram_gap_central_symm φ v k hv hzs hzt hgap
    have hhalf' := intervalDiagram_gap_central φ.symm v k hgenR hgapR
      (a := 3*v-k+1) (b := k) (by omega) (by omega) (by omega) (by omega) (by omega)
    rw [intervalDiagram_symm φ (3*v) (3*v-k+1) k (by omega),
      show 3*v-(3*v-k+1)=k-1 by omega] at hhalf'
    have hSA : ⁅(S : Subgroup G),X (3*v-k) (k-1)⁆ ≤ X (3*v-k+1) (k-1) :=
      hhalf'.trans (hzs ▸ intervalDiagram_mono φ (by omega) (by omega))
    obtain ⟨hD,heD⟩ := intervalDiagram_gap_initial_escape φ v k hk hkw hneS hj hN hSA
      (hkernel.trans hinter.symm) hd
    obtain ⟨hDb,heDb⟩ := intervalDiagram_gap_terminal_escape φ v k hk hkw hparam hD heD
    let D := ⁅X (3*v-k) (3*v-k),X (3*v) (3*v)⁆
    let Z := ⁅D,X (3*v) (3*v)⁆
    have ht : ⁅X v v,X (3*v) (3*v)⁆ ≤ X (2*v) (2*v) := by
      simpa only [show v+2*v=3*v by omega,show v+v=2*v by omega] using htwice v le_rfl
    have hp : PointCommutatorCovering (X v v) (X (v+1) (v+1))
        (X (3*v) (3*v)) (X (3*v-1) (3*v-1)) (X (2*v) (2*v)) (X (2*v-1) (2*v-1)) := by
      simpa only [show v+2*v=3*v by omega,show v+v=2*v by omega] using (hpoint v le_rfl).2
    obtain ⟨hZ,hcover⟩ := intervalDiagram_terminal_triple_cover φ v hv
      hnum.normal_left hnum.normal_right hj hshort hzt ht hp D hDb heDb
    have hescape : ¬ Z ≤ X (2*v-1) (2*v-1) := by
      intro hh
      have hn := intervalDiagram_point_not_le_previous φ (3*v) hj hneT (2*v) (by omega) (by omega)
      exact hn (hcover.symm.le.trans (sup_le hh inf_le_right))
    have hZT : Z ≤ T.lowerCentralSeries 2 := by
      have hXT : X 1 (3*v) = T := by
        simp only [X,T,intervalDiagram,Nat.sub_self,intervalCell_initial_right]
      have hA : X (3*v-k) (3*v-k) ≤ T :=
        (intervalDiagram_mono φ (by omega) (by omega)).trans hXT.le
      have hB : X (3*v) (3*v) ≤ T :=
        (intervalDiagram_mono φ (by omega) le_rfl).trans hXT.le
      simp only [Subgroup.lowerCentralSeries_succ,Subgroup.lowerCentralSeries_zero]
      exact commutator_mono (commutator_mono hA hB) hB
    have hZomega : Z ≤ omegaCenterIn (pCore 2 G) := by
      have hω := hnum.omegaCenters_eq_centers.2.2
      rw [hinter,hzq] at hω
      rw [hω]
      exact hZ.trans (intervalDiagram_mono φ (by omega) le_rfl)
    obtain ⟨w,hw⟩ := heven
    have hvw : v = 2*w := by omega
    have hkw' : k = 5*w := by omega
    have hwpos : 0 < w := by omega
    have h6 : 3*v = 6*w := by omega
    have h4 : 2*v = 4*w := by omega
    have hl : 3*v-k = w := by omega
    have hNw : (intervalDiagram φ (6*w) (w+1) (5*w-1)).Normal := by
      rw [hl,h6,hkw'] at hN
      exact hN
    have hQn : ((S : Subgroup G) ⊓ T).Normal := hinter.symm ▸ inferInstance
    have hNVw : ⁅(⊤ : Subgroup G),intervalDiagram φ (6*w) (w+1) (5*w-1)⁆ ≤
        intervalDiagram φ (6*w) (2*w) (4*w) := by
      rw [hl,h6,h4,hvw,hkw'] at hNV
      exact hNV
    have hQMw : ⁅(⊤ : Subgroup G),(S : Subgroup G) ⊓ T⁆ ≤
        intervalDiagram φ (6*w) w (5*w) := by
      rw [hinter]
      rw [hl,h6,hkw'] at hQM
      exact hQM
    have hZw : Z ≤ intervalDiagram φ (6*w) (4*w) (4*w) := by
      change Z ≤ X (2*v) (2*v) at hZ
      simpa only [X,h6,h4] using hZ
    have hew : ¬ Z ≤ intervalDiagram φ (6*w) (4*w-1) (4*w-1) := by
      simpa only [X,h6,h4] using hescape
    have hesc := intervalDiagram_half_power_escape (S : Subgroup G) α g w hwpos Z
      hNw hQn hNVw hQMw hZw hew
    exact ⟨g,hg,hgen,hinter,w,hwpos,Z,hZomega,hZT,by rwa [hinter] at hesc⟩

/-- The actual invariant-kernel quotient for a power of the original
Sylow automorphism; its SL₂ marking is transported through the literal
quotient map. This package is a conclusion of the following theorem. -/
@[expose] def NilesPowerReduction
    (e : (G ⧸ pCore 2 G) ≃* SL(2,F)) (S : Subgroup G) (α : MulAut S) : Prop :=
  S.lowerCentralSeries 2 = ⊥ ∨
    ∃ g : G, g ∈ pResidual 2 G ∧ S ⊔ S.map (MulAut.conj g).toMonoidHom = ⊤ ∧
      S ⊓ S.map (MulAut.conj g).toMonoidHom = pCore 2 G ∧
      ∃ w : ℕ, 0 < w ∧ ∃ Z : Subgroup G,
      Z ≤ omegaCenterIn (pCore 2 G) ∧
      Z ≤ (S.map (MulAut.conj g).toMonoidHom).lowerCentralSeries 2 ∧
      let L := (invariantNormalKernel S (α^w)).map S.subtype
      let q := QuotientGroup.mk' L
      ∃ s : NoncentralChiefRefinement.SeriesOn L, (∀ i, s.Central i) ∧
        L ≤ pCore 2 G ∧ pResidual 2 G ≤ centralizer (L : Set G) ∧
        generalizedFitting (G ⧸ L) = pCore 2 (G ⧸ L) ∧
        Order.HasUniqueMaximalOver (S.map q) ⊤ ∧
        Group.nilpotencyClass ((S.map (MulAut.conj g).toMonoidHom).map q) = 3 ∧
        (∃ e' : ((G ⧸ L) ⧸ pCore 2 (G ⧸ L)) ≃* SL(2,F),
          ∀ x : G, e' (QuotientGroup.mk' (pCore 2 (G ⧸ L)) (q x)) =
            e (QuotientGroup.mk' (pCore 2 G) x)) ∧
        Z.map q ≤ omegaCenterIn (pCore 2 (G ⧸ L)) ∧
        ∃ γ : MulAut (S.map q),
          (∀ x : S, γ (q.subgroupMap S x) = q.subgroupMap S ((α^w) x)) ∧
          NoInvariantNormal (S.map q) γ ∧
          (¬ (image (twistedConjugacy (S.map q) γ (q g)))^[2] (Z.map q) ≤ pCore 2 (G ⧸ L)) ∧
          NilesTwoStepDiagram (Nat.card F) (S.map q) γ (q g)

/-- Niles 6.4--6.5 at the original degree, with all interval and survival
premises discharged and the original quotient marking retained. -/
theorem original_sl2_power_reduction
    (e : (G ⧸ pCore 2 G) ≃* SL(2,F)) {n : ℕ}
    (hn : 1 < n) (hF : Nat.card F = 2^n)
    (S : Sylow 2 G) (α : MulAut S)
    (hu : Order.HasUniqueMaximalOver (S : Subgroup G) ⊤)
    (hfit : generalizedFitting G = pCore 2 G)
    (hno : NoInvariantNormal (S : Subgroup G) α) :
    NilesPowerReduction e (S : Subgroup G) α := by
  rcases original_sl2_terminal_triple e hn hF S α hfit hno with hc | ht
  · exact Or.inl hc
  · apply Or.inr
    obtain ⟨g,hg,hgen,hinter,w,hw,Z,hZomega,hZthird,hescape⟩ := ht
    let L := (invariantNormalKernel (S : Subgroup G) (α^w)).map (S : Subgroup G).subtype
    let q := QuotientGroup.mk' L
    have hescape' : ¬ (image ((α^w).trans ((MulAut.conj g).subgroupMap
        (S : Subgroup G))))^[2] Z ≤ (S : Subgroup G) ⊓
          (S : Subgroup G).map (MulAut.conj g).toMonoidHom := by
      rwa [←twistedConjugacy_eq,hinter]
    have hsurvive : ¬ Z ≤ L :=
      not_le_invariantKernel_of_twisted_escape (S : Subgroup G) (α^w) g Z 2 hescape'
    have hV : ¬ omegaCenterIn (pCore 2 G) ≤ L := fun hh => hsurvive (hZomega.trans hh)
    have hlarge : 3 < Nat.card F := by
      rw [hF]
      have hh := Nat.pow_le_pow_right (by decide : 0 < 2) (show 2 ≤ n by omega)
      norm_num at hh
      omega
    let : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) :=
      Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by omega)
    let : IsSimpleGroup SL(2,F) :=
      (Atlas.RankOneFieldAutomorphisms.slEquivPSL (F := F)).isSimpleGroup
    let : IsSimpleGroup (G ⧸ pCore 2 G) := e.isSimpleGroup
    have hK : ¬ IsPGroup 2 (G ⧸ pCore 2 G) := by
      intro hp
      have hp' := hp.of_equiv e
      have hh : (⊤ : Subgroup SL(2,F)) ≤ pCore 2 SL(2,F) :=
        le_sSup ⟨inferInstance,hp'.to_subgroup ⊤⟩
      rw [Matrix.SL2.twoCore_eq_bot] at hh
      exact top_ne_bot (le_bot_iff.mp hh)
    obtain ⟨s,hs⟩ := invariantKernel_central_chief_of_omega_not_le S hu (pCore 2 G) hK (α^w) hV
    have hLS : L ≤ (S : Subgroup G) := map_subtype_le _
    have hpL : IsPGroup 2 L := S.isPGroup'.of_injective (inclusion hLS) (inclusion_injective hLS)
    have hLQ : L ≤ pCore 2 G := le_sSup ⟨inferInstance,hpL⟩
    have hres := residual_le_centralizer_of_central_chief_series L hpL s hs
    obtain ⟨hfitL,huL,_⟩ := invariantKernel_quotient_structure S hu hfit (α^w) hres
    have hclass : ((S : Subgroup G).map (MulAut.conj g).toMonoidHom).lowerCentralSeries 3 = ⊥ := by
      rw [←Subgroup.map_lowerCentralSeries,(original_sl2_class_three e hn hF S α hfit hno).1,
        Subgroup.map_bot]
    have hcl := nilpotencyClass_image_eq_three_of_surviving_subgroup q _ Z hclass hZthird
      (by simpa only [q,QuotientGroup.ker_mk'] using hsurvive)
    have hqker : IsPGroup 2 q.ker := by
      change IsPGroup 2 (QuotientGroup.mk' L).ker
      rw [QuotientGroup.ker_mk']
      exact hpL
    let f := q.pCoreQuotientEquiv (QuotientGroup.mk'_surjective L) hqker
    let e' := f.symm.trans e
    have he' : ∀ x : G, e' (QuotientGroup.mk' (pCore 2 (G ⧸ L)) (q x)) =
        e (QuotientGroup.mk' (pCore 2 G) x) := by
      intro x
      have hf : f (QuotientGroup.mk' (pCore 2 G) x) =
          QuotientGroup.mk' (pCore 2 (G ⧸ L)) (q x) := rfl
      rw [←hf]
      exact congrArg e (f.symm_apply_apply _)
    obtain ⟨γ,hγ,hnoγ⟩ := quotientImage_noInvariantNormal_formula (S : Subgroup G) (α^w)
    have hescγ := twice_twisted_escape_map q (QuotientGroup.mk'_surjective L) hqker
      (S : Subgroup G) (α^w) γ hγ g Z hescape
    have hcoremap : (pCore 2 G).map q = pCore 2 (G ⧸ L) := by
      rw [←q.comap_pCore_of_ker_isPGroup (QuotientGroup.mk'_surjective L) hqker,
        map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective L)]
    have hZmap : Z.map q ≤ omegaCenterIn (pCore 2 (G ⧸ L)) := by
      rintro y ⟨z,hz,rfl⟩
      obtain ⟨hzQ,hzc,hz2⟩ := (mem_omegaCenterIn_iff _ _).mp (hZomega hz)
      apply (mem_omegaCenterIn_iff _ _).mpr
      refine ⟨hcoremap ▸ mem_map_of_mem q hzQ,?_,?_⟩
      · rw [←hcoremap]
        rintro y ⟨x,hx,rfl⟩
        simpa only [map_mul] using congrArg q (hzc x hx)
      · rw [←map_pow,hz2,map_one]
    have hconj : ((S : Subgroup G).map (MulAut.conj g).toMonoidHom).map q =
        ((S : Subgroup G).map q).map (MulAut.conj (q g)).toMonoidHom := by
      rw [map_map,map_map]
      congr 1
    have hgen' : (S : Subgroup G).map q ⊔
        ((S : Subgroup G).map q).map (MulAut.conj (q g)).toMonoidHom = ⊤ := by
      rw [←hconj,←Subgroup.map_sup,hgen,map_top_of_surjective q (QuotientGroup.mk'_surjective L)]
    have hinter' : (S : Subgroup G).map q ⊓
        ((S : Subgroup G).map q).map (MulAut.conj (q g)).toMonoidHom = pCore 2 (G ⧸ L) := by
      rw [←hconj,inf_comm,←map_inf_of_ker_le q _ _ (by
        rw [QuotientGroup.ker_mk']; exact hLS),inf_comm,hinter,hcoremap]
    have hcl' : Group.nilpotencyClass
        (((S : Subgroup G).map q).map (MulAut.conj (q g)).toMonoidHom) = 3 := by
      rw [←hconj]
      exact hcl
    have hdiagram := sl2_two_step_class_three_diagram e' hn hF
      (S.mapSurjective (QuotientGroup.mk'_surjective L)) γ hfitL hnoγ (q g)
      hgen' hinter' hcl' (Z.map q) hZmap hescγ
    exact ⟨g,hg,hgen,hinter,w,hw,Z,hZomega,hZthird,s,hs,hLQ,hres,hfitL,huL,hcl,
      ⟨e',he'⟩,hZmap,γ,hγ,hnoγ,hescγ,hdiagram⟩

end Glauberman
