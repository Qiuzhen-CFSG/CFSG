module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.PointBlocks.Linear.PointCore

/-!
# Excluding the doubled-natural core at the original linear point

A nonzero coordinate projection from the original seed V onto one natural
summand is surjective by SL₃ transitivity and injective by the known order
of V. This constructs equivariant coordinates without identifying the
classification's quotient marking with the original seed marking.
Both projections then show that C_L(V₁) fixes every Sylow-fixed vector of
the doubled MS core. Odd-index averaging corrects each Sylow-central
involution into that core, proving C_LR₁(Ω₁Z(S'))=C_L(V₁)R₁ for the actual
S'=T∩LR₁. Its two-core is R₁, contradicting C.1.34(2).

The terminal theorem selects the SL₃ block from all five intrinsic
alternatives. The standalone centralizer-core theorem consumes only the
natural section data and does not require ambient fixed-factor centrality.
Source applies this to the original RadicalAssembly consumer. The intrinsic
classification remains with qt-c134-nonbinary-linear-three-source; final
normalizer assembly remains with qt-d-1222-natural-normalizer-source.
Source: Aschbacher--Smith C.1.34, printed pp.136--137, and 11.1.5, p.765.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Theory.GroupTheory Representation Matrix
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open scoped MatrixGroups IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.PointBlocks.Linear
open PointCohomology.PointGeometry.SL3Core
open Chapter1.RadicalExclusions.ModelReduction.FullSieve
open Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
  (m : ActionEquiv D.centralQuotientAction (linearNatural S.field 3))
  (f : InvariantFlag (.sl3 m))
local notation "W" => (Fin 3 → S.field.Carrier)
local notation "ρ" => (specialLinearNatural (k := S.field.Carrier) 3)

private def doubleProjection (b : Bool) : Multiplicative (W × W) →* Multiplicative W where
  toFun w := Multiplicative.ofAdd (if b then w.toAdd.1 else w.toAdd.2)
  map_one' := by cases b <;> rfl
  map_mul' := by intro x y; cases b <;> rfl

private theorem doubleProjection_action (b : Bool) (g : SL(3,S.field.Carrier))
    (w : W × W) :
    (doubleProjection D S b (Multiplicative.ofAdd (((ρ).prod ρ) g w))).toAdd =
      ρ g (doubleProjection D S b (Multiplicative.ofAdd w)).toAdd := by
  cases b <;> rfl

include m in
/-- A nonzero coordinate projection identifies the original seed with one
natural summand. The classification's marking need not equal the seed marking. -/
private theorem seed_double_coordinates {A : Subgroup G} (hVA : V ≤ A)
    (e : (L ⧸ pCore 2 L) ≃* SL(3,S.field.Carrier))
    (c : A ≃* Multiplicative (W × W))
    (hc : ∀ (l : L) (x y : A), (y : G) = l * (x : G) * (l : G)⁻¹ →
      (c y).toAdd = ((ρ).prod ρ) (linearThreeActor e l) (c x).toAdd) :
    ∃ j : V ≃* Multiplicative W,
      ∀ (l : L) (v : V),
        (j (V.normalizerMonoidHom (inclusion D.normalizes l) v)).toAdd =
          ρ (linearThreeActor e l) (j v).toAdd := by
  obtain ⟨v,hv,hv1⟩ := V.bot_or_exists_ne_one.resolve_left D.ne_bot
  let v' : V := ⟨v,hv⟩
  have hc1 : c (inclusion hVA v') ≠ 1 := by
    intro he
    exact hv1 (congrArg Subtype.val (c.injective (he.trans c.map_one.symm)))
  have hn : ∃ b : Bool, doubleProjection D S b (c (inclusion hVA v')) ≠ 1 := by
    by_cases h : doubleProjection D S true (c (inclusion hVA v')) = 1
    · refine ⟨false,fun h' => hc1 ?_⟩
      apply congrArg Multiplicative.ofAdd
      exact Prod.ext (congrArg Multiplicative.toAdd h) (congrArg Multiplicative.toAdd h')
    · exact ⟨true,h⟩
  obtain ⟨b,hb⟩ := hn
  let p : V →* Multiplicative W :=
    (doubleProjection D S b).comp (c.toMonoidHom.comp (inclusion hVA))
  have hp (l : L) (w : V) :
      (p (V.normalizerMonoidHom (inclusion D.normalizes l) w)).toAdd =
        ρ (linearThreeActor e l) (p w).toAdd := by
    have he := hc l (inclusion hVA w)
      (inclusion hVA (V.normalizerMonoidHom (inclusion D.normalizes l) w)) rfl
    change (doubleProjection D S b (c _)).toAdd = _
    have hp := congrArg (fun z : W × W =>
      (doubleProjection D S b (Multiplicative.ofAdd z)).toAdd) he
    exact hp.trans (doubleProjection_action D S b _ _)
  have hs : Function.Surjective p := by
    intro x
    by_cases hx : x = 1
    · exact ⟨1,hx ▸ p.map_one⟩
    have hv0 : (p v').toAdd ≠ 0 := fun h => hb (congrArg Multiplicative.ofAdd h)
    have hx0 : x.toAdd ≠ 0 := fun h => hx (congrArg Multiplicative.ofAdd h)
    obtain ⟨g,hg⟩ := SpecialLinearGroup.exists_mulVec_eq_three (p v').toAdd x.toAdd hv0 hx0
    obtain ⟨l,hl⟩ := (e.surjective.comp (QuotientGroup.mk'_surjective (pCore 2 L))) g
    refine ⟨V.normalizerMonoidHom (inclusion D.normalizes l) v',?_⟩
    apply Multiplicative.toAdd.injective
    rw [hp]
    change ρ (e (QuotientGroup.mk' _ l)) (p v').toAdd = x.toAdd
    change e (QuotientGroup.mk' _ l) = g at hl
    rw [hl]
    exact hg
  have hbij : Function.Bijective p :=
    (Nat.bijective_iff_surjective_and_card p).mpr ⟨hs,seed_card D S m⟩
  exact ⟨MulEquiv.ofBijective p hbij,hp⟩

private theorem section_coordinates
    (e : (L ⧸ pCore 2 L) ≃* SL(3,S.field.Carrier))
    (h : HasSectionModel L (msQ L (f.Ri 0)) ⊥ (linearThreeActor e) ((ρ).prod ρ)) :
    ∃ c : msQ L (f.Ri 0) ≃* Multiplicative (W × W),
      ∀ (l : L) (x y : msQ L (f.Ri 0)), (y : G) = l * (x : G) * (l : G)⁻¹ →
        (c y).toAdd = ((ρ).prod ρ) (linearThreeActor e l) (c x).toAdd := by
  rw [HasSectionModel,bot_subgroupOf] at h
  obtain ⟨_,_,_,hn,c,hc⟩ := h
  let := hn
  exact ⟨QuotientGroup.quotientBot.symm.trans c,hc⟩

/-- On any doubled-natural subgroup containing the original seed, fixing
the point fixes its component-Sylow fixed subgroup. This applies to the
initial moved subgroup as well as to the whole MS core. -/
theorem point_fixer_centralizes_doubled_fixed
    {A : Subgroup G} (hVA : V ≤ A)
    (e : (L ⧸ pCore 2 L) ≃* SL(3,S.field.Carrier))
    (h : HasSectionModel L (A) ⊥ (linearThreeActor e) ((ρ).prod ρ)) :
    L ⊓ centralizer (f.Vi 0 : Set G) ≤ centralizer
      ((A ⊓ centralizer (((T : Subgroup G) ⊓ L : Subgroup G) : Set G) : Subgroup G) : Set G) := by
  let Q := A
  have coords : ∃ c : A ≃* Multiplicative (W × W),
      ∀ (l : L) (x y : A), (y : G) = l * (x : G) * (l : G)⁻¹ →
        (c y).toAdd = ((ρ).prod ρ) (linearThreeActor e l) (c x).toAdd := by
    rw [HasSectionModel,bot_subgroupOf] at h
    obtain ⟨_,_,_,hn,c,hc⟩ := h
    let := hn
    exact ⟨QuotientGroup.quotientBot.symm.trans c,hc⟩
  obtain ⟨c,hc⟩ := coords
  obtain ⟨j,hj⟩ := seed_double_coordinates D S m hVA e c hc
  rintro l ⟨hl,hfix⟩ q ⟨hq,hqP⟩
  let l' : L := ⟨l,hl⟩
  let q' : Q := ⟨q,hq⟩
  have hcoord (b : Bool) :
      ρ (linearThreeActor e l') (doubleProjection D S b (c q')).toAdd =
        (doubleProjection D S b (c q')).toAdd := by
    let v := j.symm (doubleProjection D S b (c q'))
    have hJP (s : L) (hs : (s : G) ∈ (T : Subgroup G)) :
        V.normalizerMonoidHom (inclusion D.normalizes s) v = v := by
      apply j.injective
      apply Multiplicative.toAdd.injective
      rw [hj,j.apply_symm_apply]
      have he := hc s q' q' (by
        change q = (s : G)*q*(s : G)⁻¹
        rw [hqP s ⟨hs,s.property⟩,mul_inv_cancel_right])
      have hp := congrArg (fun w : W × W =>
        (doubleProjection D S b (Multiplicative.ofAdd w)).toAdd) he
      rw [doubleProjection_action] at hp
      exact hp.symm
    have hv : (v : G) ∈ f.Vi 0 := by
      rw [←local_core_fixed D S m f]
      refine ⟨v.property,?_⟩
      intro s hs
      have hsL : s ∈ L := ((pCoreIn_le 2 _).trans
        ((localResidual_le _).trans inf_le_left)) hs
      have hsR : s ∈ f.Ri 0 :=
        pCoreIn_mono_of_normalizes le_sup_left
          (sup_le (f.Li 0).le_normalizer (f.sylow_normalizes_Li 0)) hs
      have he := congrArg Subtype.val (hJP ⟨s,hsL⟩ (localRadical_le_sylow _ hsR))
      exact mul_inv_eq_iff_eq_mul.mp he
    have he := hj l' v
    have hf : V.normalizerMonoidHom (inclusion D.normalizes l') v = v := by
      apply Subtype.ext
      change l * (v : G) * l⁻¹ = (v : G)
      rw [←hfix v hv,mul_inv_cancel_right]
    rw [hf] at he
    simpa only [v,j.apply_symm_apply] using he.symm
  let qconj : Q := ⟨l*q*l⁻¹,(h.2.1 hl q).mp hq⟩
  have he := hc l' q' qconj rfl
  have heq : c qconj = c q' := by
    apply Multiplicative.toAdd.injective
    rw [he]
    exact Prod.ext (hcoord true) (hcoord false)
  have heq' := congrArg Subtype.val (c.injective heq)
  exact (mul_inv_eq_iff_eq_mul.mp heq').symm

/-- In the doubled-natural row, fixing the original point fixes every vector
of the MS core centralized by the actual component Sylow intersection. -/
theorem double_point_fixer_centralizes_fixed_core
    (e : (L ⧸ pCore 2 L) ≃* SL(3,S.field.Carrier))
    (h : HasSectionModel L (msQ L (f.Ri 0)) ⊥ (linearThreeActor e) ((ρ).prod ρ)) :
    L ⊓ centralizer (f.Vi 0 : Set G) ≤ centralizer
      ((msQ L (f.Ri 0) ⊓ centralizer (((T : Subgroup G) ⊓ L : Subgroup G) : Set G) : Subgroup G) : Set G) :=
  point_fixer_centralizes_doubled_fixed D S m f (seed_le_msQ D S f) e h

/-- Odd-index averaging in the genuine doubled core, followed by its two
natural projections, identifies the actual Sylow-omega centralizer. -/
theorem double_component_centralizer
    (e : (L ⧸ pCore 2 L) ≃* SL(3,S.field.Carrier))
    (h : HasSectionModel L (msQ L (f.Ri 0)) ⊥ (linearThreeActor e) ((ρ).prod ρ)) :
    L ⊓ centralizer (Subgroup.omegaCenterIn ((T : Subgroup G) ⊓ (L ⊔ f.Ri 0)) : Set G) =
      L ⊓ centralizer (f.Vi 0 : Set G) := by
  apply le_antisymm (omega_fixer_le_point_fixer D S m f)
  let Q := msQ L (f.Ri 0)
  let N := (L ⊔ f.Ri 0).pCoreIn 2
  obtain ⟨c,hc⟩ := section_coordinates D S m f e h
  let : IsMulCommutative Q := IsMulCommutative.of_comm (fun x y =>
    c.injective (by rw [map_mul,map_mul,mul_comm]))
  have hexp : ∀ q ∈ Q, q^2 = 1 := by
    intro q hq
    have he : (⟨q,hq⟩ : Q)^2 = 1 := by
      apply c.injective
      rw [map_pow,map_one,pow_two]
      apply Multiplicative.toAdd.injective
      change (c ⟨q,hq⟩).toAdd + (c ⟨q,hq⟩).toAdd = 0
      exact Prod.ext (funext fun i => CharTwo.add_self_eq_zero _)
        (funext fun i => CharTwo.add_self_eq_zero _)
    exact congrArg Subtype.val he
  obtain ⟨P,hP⟩ := NormalSylowQuotientAction.intersection_sylow T L D.sylow_normalizes_component
  have hPA : (P : Subgroup L).map L.subtype = (T : Subgroup G) ⊓ L := by
    rw [hP,subgroupOf_map_subtype]
  have hNA : N ≤ (T : Subgroup G) ⊓ (L ⊔ f.Ri 0) := by
    have hh := pCoreIn_le_sylow (L ⊔ f.Ri 0) (pointSylow D S f)
    rwa [pointSylow_map] at hh
  rintro l ⟨hl,hfix⟩
  refine ⟨hl,?_⟩
  intro z hz
  obtain ⟨hzS,hzc,_⟩ := (mem_omegaCenterIn_iff _ _).mp hz
  have hzN : z ∈ N := pointCore_selfCentralizing D S m f
    ⟨hzS.2,centralizer_le hNA hzc⟩
  have hzP : z ∈ centralizer ((P : Subgroup L).map L.subtype : Set G) := by
    rw [hPA]
    exact centralizer_le (show (T : Subgroup G) ⊓ L ≤
      (T : Subgroup G) ⊓ (L ⊔ f.Ri 0) from inf_le_inf_left _ le_sup_left) hzc
  obtain ⟨q,hq,hqz⟩ := fixed_coset_of_sylow L Q h.2.1 hexp P z
    (fun a ha => by
      change ⁅a,z⁆ ∈ ⁅N,L⁆
      rw [commutator_comm]
      exact commutator_mem_commutator ha hzN)
    (fun a ha => hzP a (mem_map_of_mem L.subtype ha))
  have hqP : q ∈ centralizer (((T : Subgroup G) ⊓ L : Subgroup G) : Set G) := by
    rw [←hPA]
    have hh := (centralizer ((P : Subgroup L).map L.subtype : Set G)).mul_mem
      (centralizer_le (map_subtype_le _) hqz) ((centralizer _).inv_mem hzP)
    simpa only [mul_inv_cancel_right] using hh
  have hqc := double_point_fixer_centralizes_fixed_core D S m f e h ⟨hl,hfix⟩ q ⟨hq,hqP⟩
  have hqzc := hqz l hl
  apply mul_left_cancel (a := q)
  calc
    q * (z*l) = (q*z)*l := (mul_assoc _ _ _).symm
    _ = l*(q*z) := hqzc.symm
    _ = (l*q)*z := (mul_assoc _ _ _).symm
    _ = (q*l)*z := by rw [hqc]
    _ = q*(l*z) := mul_assoc _ _ _

/-- The point computation consumes only the indicated natural section and
returns the exact centralizer-core identity. In particular the field-four
fixed factor need not centralize LR₁. -/
theorem model_rows_centralizer_core
    (e : (L ⧸ pCore 2 L) ≃* SL(3,S.field.Carrier))
    (h : HasSectionModel L (msQ L (f.Ri 0)) ⊥ (linearThreeActor e) ((ρ).prod ρ) ∨
      HasSectionModel L (SourceInterface.centerIn (msQ L (f.Ri 0))) ⊥
        (linearThreeActor e) ρ ∨
      HasSectionModel L ⁅SourceInterface.centerIn (msQ L (f.Ri 0)),L⁆ ⊥
        (linearThreeActor e) ρ) :
    ((L ⊔ f.Ri 0) ⊓ centralizer
      (Subgroup.omegaCenterIn ((T : Subgroup G) ⊓ (L ⊔ f.Ri 0)) : Set G)).pCoreIn 2 =
        f.Ri 0 := by
  rcases h with hd | hz
  · rw [omega_centralizer_join D S m f,double_component_centralizer D S m f e hd,
      point_fixer_core D S m f]
  · rw [central_cases_join_centralizer D S m f e hz,point_fixer_core D S m f]

/-- Only the intrinsic section data and inequalities consumed by the point
argument. No fixed-factor centrality or unused upper-core section is required. -/
def PointModuleCases (R U : Subgroup G)
    (e : (L ⧸ pCore 2 L) ≃* SL(3,S.field.Carrier)) : Prop :=
  ChapterC.IsSL3EvenBlock L S.field.degree ∨
  ((HasSectionModel L (msQ L R) ⊥ (linearThreeActor e) ((ρ).prod ρ) ∨
    HasSectionModel L (SourceInterface.centerIn (msQ L R)) ⊥ (linearThreeActor e) ρ ∨
    HasSectionModel L ⁅SourceInterface.centerIn (msQ L R),L⁆ ⊥ (linearThreeActor e) ρ) ∧
      MSNotCentralizerCore L R U) ∨
  SourceInterface.omegaCenterIn U ≤ SourceInterface.centerIn (L ⊔ R)

/-- The existing full C.1.34 interface supplies the precise smaller input.
A corrected intrinsic classifier may instead construct these clauses directly. -/
theorem pointModuleCases_of_alternatives (R U : Subgroup G)
    (e : (L ⧸ pCore 2 L) ≃* SL(3,S.field.Carrier))
    (h : MSModuleAlternatives L R U S.field.degree S.field.Carrier e) :
    PointModuleCases D S R U e := by
  rcases h with h1 | h2 | h3 | h4 | h5
  · exact Or.inl h1.2.1
  · exact Or.inr (Or.inl ⟨Or.inl h2.1,h2.2⟩)
  · exact Or.inr (Or.inl ⟨Or.inr (Or.inl h3.1),h3.2.2⟩)
  · exact Or.inr (Or.inl ⟨Or.inr (Or.inr h4.2.2.2.2.2.1),h4.2.2.2.2.2.2.2.2.2⟩)
  · exact Or.inr (Or.inr h5.2.2.2.1)

/-- Select the genuine block using only the minimal intrinsic point input. -/
theorem block_of_pointModuleCases
    (e : (L ⧸ pCore 2 L) ≃* SL(3,S.field.Carrier))
    (h : PointModuleCases D S (f.Ri 0) ((T : Subgroup G) ⊓ (L ⊔ f.Ri 0)) e) :
    ChapterC.IsSL3EvenBlock L S.field.degree := by
  rcases h with hb | ⟨hm,hn⟩ | hz
  · exact hb
  · exact (hn (model_rows_centralizer_core D S m f e hm).symm).elim
  · exact (pointSylow_omega_not_central D S m f hz).elim

/-- Every nonblock C.1.34 alternative is excluded for the actual point radical.
The only input left is the intrinsic classification, owned independently. -/
theorem block_of_module_alternatives
    (e : (L ⧸ pCore 2 L) ≃* SL(3,S.field.Carrier))
    (h : MSModuleAlternatives L (f.Ri 0) ((T : Subgroup G) ⊓ (L ⊔ f.Ri 0))
      S.field.degree S.field.Carrier e) : ChapterC.IsSL3EvenBlock L S.field.degree := by
  rcases alternatives_block_or_double D S m f e h with hb | ⟨hd,hn⟩
  · exact hb
  · apply False.elim
    apply hn
    change f.Ri 0 = ((L ⊔ f.Ri 0) ⊓ centralizer
      (Subgroup.omegaCenterIn ((T : Subgroup G) ⊓ (L ⊔ f.Ri 0)) : Set G)).pCoreIn 2
    rw [omega_centralizer_join D S m f,double_component_centralizer D S m f e hd,
      point_fixer_core D S m f]

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.PointBlocks.Linear
