module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.SteinbergRecognition.ModuleRecognition.ParabolicSeed.Contracts
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.SteinbergRecognition.ModuleRecognition.ParabolicSeed.LocalAction.Coordinates
public import Theory.AtlasPort.OtherSporadic.GroupTheory.CoprimeNormalTransitivity
public import Theory.GroupTheory.PResidual.NormalSubgroup
public import Theory.GroupTheory.PResidual.PerfectCover

/-!
# The original residual action on the U/V plane

The actual stabilizer N_H(V) acts transitively on the nonzero cosets of the
natural image of V/V₁: use the SL₂(4) plane-stabilizer calculation and lift
through the original qH. Its two-residual remains transitive, since its index
is a power of two and the orbit has three points. The source equality
N_G(V) = LT and T-normalization of L place this residual in L; two-perfectness
then places it in the original L₁ = O²(L ∩ H).

Finally transport those conjugating elements to the literal image of U in
S/V, using the representative equation of the given action for the original
qL. The resulting `localTransitive` discharges the published `LocalTransitive`
contract in the seed construction. No compatible actor marking, local
irreducibility, or generation identity is an additional premise.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
proof of 14.7.72, printed p.1076 (PDF p.1093), and its application of
H.6.5, printed p.388 (PDF p.399).
-/

@[expose] public section
noncomputable section
open Subgroup Representation
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.SteinbergRecognition.ModuleRecognition.ParabolicSeed.LocalAction
open Chapter12.Section08 CriticalFusion.Source
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {F : InvariantFlag T V 3}
  {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
  (d : Data T L V F W)

/-- The literal ambient stabilizer, before passing to any residual. -/
def actor : Subgroup G := F.H ⊓ normalizer (V : Set G)

/-- The natural action retains the original star map on this stabilizer. -/
def actorAction : Representation (ZMod 2) (actor (F := F)) SL2FourNatural.V :=
  d.naturalQuotient.action.comp (d.qH.comp (Subgroup.inclusion inf_le_left))

/-- The actual V-image is invariant under its ambient stabilizer. -/
def actorPlane (hU₀ : d.U₀ = F.Vi 1) : Subrepresentation (actorAction d) where
  toSubmodule := seedPlane d
  apply_mem_toSubmodule h v hv := by
    obtain ⟨u, rfl⟩ := naturalCoordinates_surjective d (Multiplicative.ofAdd v)
    have hu := (coordinates_mem_seedPlane d hU₀ u).mp hv
    change d.naturalQuotient.action (d.qH (Subgroup.inclusion inf_le_left h))
      (naturalCoordinates d u).toAdd ∈ seedPlane d
    rw [← naturalCoordinates_equivariant]
    apply (coordinates_mem_seedPlane d hU₀ _).mpr
    exact (mem_normalizer_iff.mp h.property.2 u).mp hu

/-- The ambient stabilizer is transitive on the nonzero cosets of the
literal seed image. The lifts are taken through the original qH. -/
theorem actor_transitive (hU₀ : d.U₀ = F.Vi 1)
    (v w : SL2FourNatural.V ⧸ seedPlane d) (hv : v ≠ 0) (hw : w ≠ 0) :
    ∃ h : actor (F := F), (actorPlane d hU₀).quotientRepresentation h v = w := by
  obtain ⟨x, rfl⟩ := (seedPlane d).mkQ_surjective v
  obtain ⟨y, rfl⟩ := (seedPlane d).mkQ_surjective w
  obtain ⟨g, hg, he⟩ := SL2FourNatural.plane_quotient_transitive (seedPlane d)
    (card_seedPlane d hU₀) x y
    (fun hx => hv ((Submodule.Quotient.mk_eq_zero _).mpr hx))
    (fun hy => hw ((Submodule.Quotient.mk_eq_zero _).mpr hy))
  obtain ⟨h, hn, hh⟩ := lift_plane_stabilizer d hU₀ g hg
  refine ⟨⟨h.val, h.property, hn⟩, ?_⟩
  change (seedPlane d).mkQ (d.naturalQuotient.action (d.qH h) x) = (seedPlane d).mkQ y
  rw [hh, d.naturalQuotient.restriction]
  exact ((Submodule.Quotient.eq _).mpr he).symm

private theorem residual_transitive_on_four
    {A X : Type*} [Group A] [Finite A] [AddCommGroup X] [Module (ZMod 2) X]
    [Finite X] (ρ : Representation (ZMod 2) A X) (hX : Nat.card X = 4)
    (htrans : ∀ v w : X, v ≠ 0 → w ≠ 0 → ∃ a, ρ a v = w)
    (v w : X) (hv : v ≠ 0) (hw : w ≠ 0) :
    ∃ a : A, a ∈ pResidual 2 A ∧ ρ a v = w := by
  classical
  let Ω := {x : X // x ≠ 0}
  have hnot (a : A) (x : Ω) : ρ a x.val ≠ 0 := by
    intro he
    apply x.property
    have h := congrArg (ρ a⁻¹) he
    simpa only [map_zero, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel,
      map_one, Module.End.one_apply] using h
  let : MulAction A Ω := {
    smul a x := ⟨ρ a x.val, hnot a x⟩
    one_smul x := by apply Subtype.ext; exact congrArg (fun f => f x.val) ρ.map_one
    mul_smul a b x := by apply Subtype.ext; exact congrArg (fun f => f x.val) (ρ.map_mul a b) }
  let : MulAction.IsPretransitive A Ω := ⟨by
    intro x y
    obtain ⟨a, ha⟩ := htrans x.val y.val x.property y.property
    exact ⟨a, Subtype.ext ha⟩⟩
  have hΩ : Nat.card Ω = 3 := by
    let := Fintype.ofFinite X
    change Nat.card {x : X // ¬ x = 0} = 3
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl]
    simp only [Fintype.card_unique, ← Nat.card_eq_fintype_card, hX]
  obtain ⟨n, hn⟩ := (isPGroup_quotient_pResidual (G := A) 2).exists_card_eq
  have hcop : Nat.Coprime (pResidual 2 A).index (Nat.card Ω) := by
    rw [index_eq_card, hn, hΩ]
    exact (by decide : Nat.Coprime 2 3).pow_left n
  let := Atlas.GroupTheory.normal_transitive_of_coprime_index (X := Ω) (pResidual 2 A) hcop
  obtain ⟨a, ha⟩ := MulAction.exists_smul_eq (pResidual 2 A) (⟨v, hv⟩ : Ω) ⟨w, hw⟩
  exact ⟨a.val, a.property, congrArg Subtype.val ha⟩

/-- The same transitivity holds for the two-residual of N_H(V). -/
theorem actor_residual_transitive (hU₀ : d.U₀ = F.Vi 1)
    (v w : SL2FourNatural.V ⧸ seedPlane d) (hv : v ≠ 0) (hw : w ≠ 0) :
    ∃ h : actor (F := F), h ∈ pResidual 2 (actor (F := F)) ∧
      (actorPlane d hU₀).quotientRepresentation h v = w := by
  apply residual_transitive_on_four _ _ (actor_transitive d hU₀) v w hv hw
  have hc := (seedPlane d).card_eq_card_quotient_mul_card
  rw [card_seedPlane d hU₀,
    show Nat.card SL2FourNatural.V = 16 by
      rw [Nat.card_eq_fintype_card, SL2FourNatural.card_vector]] at hc
  omega

/-- Relative normality and the two-group supplement place the ambient
stabilizer's two-residual in the original L₁. No containment S ≤ L is used. -/
theorem actor_residual_le_first (hs : d.ModuleSeparation)
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G)) :
    (pResidual 2 (actor (F := F))).map (actor (F := F)).subtype ≤ F.Li L 1 := by
  let M := L ⊔ (T : Subgroup G)
  let B := actor (F := F)
  let R := (pResidual 2 B).map B.subtype
  have hBM : B ≤ M := by
    exact inf_le_right.trans (d.lemma_14_7_67_five hs).ge
  let : (L.subgroupOf M).Normal :=
    normal_subgroupOf_of_le_normalizer (sup_le L.le_normalizer hTL)
  have hsup : L.subgroupOf M ⊔ (T : Subgroup G).subgroupOf M = ⊤ := by
    apply map_injective M.subtype_injective
    rw [Subgroup.map_sup, map_subgroupOf_eq_of_le le_sup_left,
      map_subgroupOf_eq_of_le le_sup_right, ← MonoidHom.range_eq_map, range_subtype]
  have hp := isPGroup_quotient_of_sup_eq_top (L.subgroupOf M)
    ((T : Subgroup G).subgroupOf M) T.isPGroup'.comap_subtype hsup
  let f : B →* M ⧸ L.subgroupOf M :=
    (QuotientGroup.mk' (L.subgroupOf M)).comp (Subgroup.inclusion hBM)
  have hk : pResidual 2 B ≤ f.ker := sInf_le ⟨inferInstance,
    (hp.to_subgroup f.range).of_equiv (QuotientGroup.quotientKerEquivRange f).symm⟩
  have hRL : R ≤ L := by
    rintro _ ⟨b, hb, rfl⟩
    exact (QuotientGroup.eq_one_iff (Subgroup.inclusion hBM b)).mp
      (MonoidHom.mem_ker.mp (hk hb))
  have hRI : R ≤ L ⊓ F.H := le_inf hRL ((map_subtype_le _).trans inf_le_left)
  have hpR : IsPPerfect 2 (R.subgroupOf (L ⊓ F.H)) :=
    (isPPerfect_embedded_pResidual 2 B).of_surjective
      (subgroupOfEquivOfLe hRI).symm.toMonoidHom (subgroupOfEquivOfLe hRI).symm.surjective
  have hr := map_mono (f := (L ⊓ F.H).subtype)
    (le_pResidual_of_isPPerfect (R.subgroupOf (L ⊓ F.H)) hpR)
  rw [map_subgroupOf_eq_of_le hRI] at hr
  change R ≤ (pResidual 2 (L ⊓ F.H : Subgroup G)).map (L ⊓ F.H).subtype
  exact hr

variable [(V.subgroupOf (S F L)).Normal]
  [IsElementaryAbelian 2 (S F L ⧸ V.subgroupOf (S F L))]

/-- Nonzero vectors of the original U/V plane are conjugate under the
original first residual, acting through the original qL. This discharges the
local-action premise of `ParabolicSeed.exists_seed_of_local_transitive`. -/
theorem localTransitive (a : QuotientAction d) (hs : d.ModuleSeparation)
    (hU₀ : d.U₀ = F.Vi 1)
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G)) : LocalTransitive d a := by
  intro v w hv hw hv0 hw0
  obtain ⟨s, hsU, rfl⟩ := (mem_plane_iff v).mp hv
  obtain ⟨t, htU, rfl⟩ := (mem_plane_iff w).mp hw
  let u : F.U := ⟨s.val, hsU⟩
  let z : F.U := ⟨t.val, htU⟩
  have huV : (u : G) ∉ V := fun he => hv0 ((QuotientGroup.eq_one_iff s).mpr he)
  have hzV : (z : G) ∉ V := fun he => hw0 ((QuotientGroup.eq_one_iff t).mpr he)
  have hu0 : (seedPlane d).mkQ (naturalCoordinates d u).toAdd ≠ 0 := by
    intro he
    exact huV ((coordinates_mem_seedPlane d hU₀ u).mp ((Submodule.Quotient.mk_eq_zero _).mp he))
  have hz0 : (seedPlane d).mkQ (naturalCoordinates d z).toAdd ≠ 0 := by
    intro he
    exact hzV ((coordinates_mem_seedPlane d hU₀ z).mp ((Submodule.Quotient.mk_eq_zero _).mp he))
  obtain ⟨h, hh, he⟩ := actor_residual_transitive d hU₀ _ _ hu0 hz0
  have hh₁ : (h : G) ∈ F.Li L 1 := actor_residual_le_first d hs hTL ⟨h, hh, rfl⟩
  let l : L := ⟨h.val, (F.Li_le L 1 hh₁).1⟩
  let c : F.U := ⟨(h : G) * (u : G) * (h : G)⁻¹,
    (mem_normalizer_iff.mp (d.conjugationSection.normalized h.property.1) u).mp u.property⟩
  have he' : (seedPlane d).mkQ (naturalCoordinates d c).toAdd =
      (seedPlane d).mkQ (naturalCoordinates d z).toAdd := by
    rw [naturalCoordinates_equivariant d ⟨h.val, h.property.1⟩ u]
    exact he
  have hcz : ((c / z : F.U) : G) ∈ V := by
    apply (coordinates_mem_seedPlane d hU₀ (c / z)).mp
    rw [map_div]
    exact (Submodule.Quotient.eq _).mp he'
  refine ⟨l, hh₁, ?_⟩
  rw [← a.equivariant]
  change QuotientGroup.mk' (V.subgroupOf (S F L)) _ = QuotientGroup.mk' _ t
  apply QuotientGroup.eq_iff_div_mem.mpr
  exact hcz

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.SteinbergRecognition.ModuleRecognition.ParabolicSeed.LocalAction
