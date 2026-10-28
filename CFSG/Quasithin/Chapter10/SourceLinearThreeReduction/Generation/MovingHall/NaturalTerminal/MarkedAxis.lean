module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.MovingHall.NaturalTerminal.AlphaEntrance
public import CFSG.Quasithin.Chapter10.SourceA5OffenderFixedGeometry

/-!
# Fixed alpha points select an axis of the original marked quotient

The two moved full-module factors have trivial intersection after the
Sylow fixed center vanishes. A nonzero fixed alpha point therefore has a
nonzero fixed coordinate in one factor. The natural SL₂ odd-order
fixed-vector calculation kills the corresponding quotient coordinate of
every element of the prescribed Hall subgroup. The exchange formula
retains the original conjugate component and quotient marking.

This identifies the axis using the original component field and action,
without comparing it to a separately selected paired representation.
Natural marking and Hall containment remain the earlier obligations of
this moving-Hall task. Source: Aschbacher–Smith 10.2.3(4), pp.746–747.
-/

public noncomputable section
open Subgroup Stellmacher Theory.GroupTheory Representation
open scoped MatrixGroups Pointwise IsMulCommutative
namespace CFSG.Quasithin.Chapter10.MovingHall
open Chapter3.Section02 ChapterB
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
  {F : Type} [Field F] [Finite F] [CharP F 2]
local instance markedAxisFieldAlgebra : Algebra (ZMod 2) F := ZMod.algebra F 2
local instance markedAxisMovedElementary : IsElementaryAbelian 2 (⁅D.fullModule,L⁆ : Subgroup G) :=
  source_original_full_moved_elementary D
set_option backward.isDefEq.respectTransparency false

private theorem marked_pair_split
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hcross : (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom ≤ centralizer (L : Set G))
    (hz : omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (localOrbit T L : Set G) = ⊥) :
    sourceMovedFixed D = ⊥ ∧
      Disjoint (⁅D.fullModule,L⁆) ((⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom) ∧
      D.fullModule = ⁅D.fullModule,L⁆ ⊔ (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom := by
  let W := ⁅D.fullModule,L⁆
  have hSW : (T : Subgroup G) ⊓ normalizer (L : Set G) ≤ normalizer (W : Set G) := by
    intro g hg
    apply mem_normalizer_iff_map_conj_eq.mpr
    change (⁅D.fullModule,L⁆).map (MulAut.conj g).toMonoidHom = _
    have hV : D.fullModule.map (MulAut.conj g).toMonoidHom = D.fullModule :=
      mem_normalizer_iff_map_conj_eq.mp
        (D.maximalLocal_normalizes_fullModule (le_normalizer_componentOrbit L T hg.1))
    have hL : L.map (MulAut.conj g).toMonoidHom = L := mem_normalizer_iff_map_conj_eq.mp hg.2
    rw [map_commutator,hV,hL]
  have htwice := conjugate_twice_eq_of_index_two W (T : Subgroup G)
    (normalizer (L : Set G))
    (source_nonnormal_sylow_stabilizer_index D.simpleQTKE D.maximal.1 hn) hSW ht
  have hWLt : W ≤ centralizer (L.map (MulAut.conj t).toMonoidHom : Set G) := by
    have hh := map_mono (f := (MulAut.conj t).toMonoidHom) hcross
    rw [htwice,Theory.GroupTheory.map_centralizer_equiv] at hh
    exact hh
  have hpair : localOrbit T L = L ⊔ L.map (MulAut.conj t).toMonoidHom :=
    componentOrbit_eq_sup_of_index_two L T (normalizer (L : Set G))
      (source_nonnormal_sylow_stabilizer_index D.simpleQTKE D.maximal.1 hn) inf_le_right ht htn
  have hRC : localOrbit T L ≤ centralizer (sourceMovedFixed D : Set G) := by
    rw [hpair]
    exact sup_le (le_centralizer_iff.mpr inf_le_right)
      (le_centralizer_iff.mpr (inf_le_left.trans hWLt))
  have hu := Chapter1.Section02.nonsolvable_uniqueness_of_theoremsAC
    (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
    (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X))
    D.simpleQTKE T D.maximal
  have hWV : W ≤ D.fullModule := le_normalizer_iff_commutator_le_left.mp
    (((le_componentOrbit L T).trans (localOrbit T L).le_normalizer).trans
      D.maximalLocal_normalizes_fullModule)
  have hk : sourceMovedFixed D = ⊥ := bot_unique
    ((le_inf (inf_le_left.trans (hWV.trans (D.fullModule_le_sylow hu)))
      (le_centralizer_iff.mp hRC)).trans (source_sylow_orbit_centralizer_eq_bot hz).le)
  refine ⟨hk,?_,source_nonnormal_fullModule_eq_moved_pair D hn ht hcross⟩
  rw [disjoint_iff]
  exact bot_unique ((le_inf inf_le_left (inf_le_right.trans hcross)).trans hk.le)

omit [Finite G] in
private theorem fixed_factors {A B : Subgroup G} (hd : Disjoint A B)
    {a b p : G} (ha : a ∈ A) (hb : b ∈ B)
    (hpA : p ∈ normalizer (A : Set G)) (hpB : p ∈ normalizer (B : Set G))
    (hf : p*(a*b)*p⁻¹ = a*b) : p*a*p⁻¹ = a ∧ p*b*p⁻¹ = b := by
  have he : (⟨⟨p*a*p⁻¹,(mem_normalizer_iff.mp hpA a).mp ha⟩,
      ⟨p*b*p⁻¹,(mem_normalizer_iff.mp hpB b).mp hb⟩⟩ : A × B) = ⟨⟨a,ha⟩,⟨b,hb⟩⟩ := by
    apply Subgroup.mul_injective_of_disjoint hd
    change (p*a*p⁻¹)*(p*b*p⁻¹) = a*b
    calc
      _ = p*(a*b)*p⁻¹ := by group
      _ = _ := hf
  exact ⟨congrArg (fun x : A × B => (x.1:G)) he,
    congrArg (fun x : A × B => (x.2:G)) he⟩

/-- A fixed alpha point selects an axis of the prescribed original quotient. -/
theorem Context.original_marked_axis_of_alpha_fixed
    {H : Subgroup G} {B : Subgroup H} (ctx : Context D H B)
    (degree : ℕ) (hdegree : 1 < degree) (hF : Nat.card F = 2 ^ degree)
    (e : (L ⧸ pCore 2 L) ≃* SL(2,F))
    (c : BinaryConjugationSection L ⁅D.fullModule,L⁆ (sourceMovedFixed D)
      (SL2.BinarySmall.natural.comp (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L)))))
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hcross : (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom ≤ centralizer (L : Set G))
    (hBR : B.map H.subtype ≤ localOrbit T L)
    (q : localOrbit T L →* (SL(2,F) × SL(2,F)))
    (hfirst : ∀ l : L, q ⟨l,le_componentOrbit L T l.property⟩ = (e (QuotientGroup.mk' _ l),1))
    (hsecond : ∀ l : L, q (originalConjugateOrbitInclusion ht l) = (1,e (QuotientGroup.mk' _ l)))
    (P : Subgroup G) (hPB : P ≤ B.map H.subtype)
    (hfixed : thompsonAlpha (T : Subgroup G) ⊓ centralizer (P : Set G) ≠ ⊥) :
    P ≤ ((MonoidHom.fst _ _).comp q).ker.map (localOrbit T L).subtype ∨
      P ≤ ((MonoidHom.snd _ _).comp q).ker.map (localOrbit T L).subtype := by
  let R := localOrbit T L
  let W := ⁅D.fullModule,L⁆
  let Wt := W.map (MulAut.conj t).toMonoidHom
  have mark : NaturalMarking D e := ⟨⟨c⟩,t,ht,htn,hcross⟩
  have hz := (ctx.fixed_centers_of_natural_marking D degree hdegree hF e mark hBR).1
  obtain ⟨hk,hd,hpair⟩ := marked_pair_split D ctx.nonnormal ht htn hcross hz
  let cR := source_original_natural_first_orbit_section D ctx.nonnormal ht htn hcross e c
    q hfirst hsecond
  have hi : Function.Injective cR.coordinates := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    rw [cR.kernel_eq,hk,bot_subgroupOf]
  have hRt : R.map (MulAut.conj t).toMonoidHom = R :=
    mem_normalizer_iff_map_conj_eq.mp (le_normalizer_componentOrbit L T ht)
  have hRWt : R ≤ normalizer (Wt : Set G) := by
    have hh := map_mono (f := (MulAut.conj t).toMonoidHom) cR.normalized
    rwa [hRt,map_normalizer_eq_of_bijective W (MulAut.conj t).bijective] at hh
  obtain ⟨⟨x,hx⟩,hne'⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hfixed
  have hne : x ≠ 1 := fun he => hne' (Subtype.ext he)
  have hxV : x ∈ D.fullModule :=
    ((ctx.original_alpha_le_moved D degree hdegree hF e mark hBR).trans
      ((le_normalizer_iff_commutator_le_left.mp D.orbit_normalizes_module).trans
        (le_componentOrbit D.moduleSubgroup D.maximalLocal))) hx.1
  have hcomm : Wt ≤ normalizer (W : Set G) := by
    have hWV : W ≤ D.fullModule := hpair ▸ le_sup_left
    have hWtV : Wt ≤ D.fullModule := hpair ▸ le_sup_right
    have hu := Chapter1.Section02.nonsolvable_uniqueness_of_theoremsAC
      (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
      (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X))
      D.simpleQTKE T D.maximal
    let := D.fullModule_elementary hu
    exact (hWtV.trans (D.fullModule.le_centralizer.trans (centralizer_le hWV))).trans
      (centralizer_le_normalizer W)
  have hxprod : x ∈ (W : Set G) * Wt := by
    rw [←coe_mul_of_right_le_normalizer_left W Wt hcomm,←hpair]
    exact hxV
  obtain ⟨w,hw,z,hzW,rfl⟩ := hxprod
  have hPfix (p : P) :
      (p:G)*w*(p:G)⁻¹ = w ∧ (p:G)*z*(p:G)⁻¹ = z :=
    fixed_factors hd hw hzW (cR.normalized (hBR (hPB p.property)))
      (hRWt (hBR (hPB p.property))) (by rw [hx.2 p p.property,mul_inv_cancel_right])
  have hodd : Odd (Nat.card P) := ctx.odd_card_of_le_hall_image P hPB
  have hfirstzero (b : R) (v : W) (hv : v ≠ 1)
      (hb : b ^ Nat.card P = 1) (hfix : (b:G)*(v:G)*(b:G)⁻¹ = v) : (q b).1 = 1 := by
    by_contra hnontriv
    have hpow : (q b).1 ^ Nat.card P = 1 := by
      have hh := congrArg (fun z => (q z).1) hb
      simpa only [map_pow,map_one,Prod.pow_fst,Prod.fst_one] using hh
    have he := cR.equivariant b v
    have hvf : (⟨(b:G)*v*(b:G)⁻¹,
      (mem_normalizer_iff.mp (cR.normalized b.property) v).mp v.property⟩ : W) = v :=
      Subtype.ext hfix
    rw [hvf] at he
    have hv0 := Matrix.SL2.odd_power_fixed_eq_zero (q b).1 (Nat.card P) hodd hpow hnontriv
      (cR.coordinates v).toAdd he.symm
    apply hv
    apply hi
    exact (Multiplicative.toAdd.injective hv0).trans cR.coordinates.map_one.symm
  by_cases hw1 : w = 1
  · right
    obtain ⟨v,hv,hvz⟩ := mem_map.mp hzW
    change t*v*t⁻¹ = z at hvz
    have hv1 : v ≠ 1 := by
      intro he
      apply hne
      rw [hw1,←hvz,he]
      simp
    intro p hp
    let b : R := ⟨p,hBR (hPB hp)⟩
    let b' := (originalOrbitConjugation ht).symm b
    have hbpow : b ^ Nat.card P = 1 := Subtype.ext
      (congrArg (fun x : P => (x:G)) (pow_card_eq_one' (x := (⟨p,hp⟩ : P))))
    have hb'pow : b' ^ Nat.card P = 1 := by
      rw [←map_pow,hbpow,map_one]
    have hf : (b':G)*v*(b':G)⁻¹ = v := by
      have hh := (hPfix ⟨p,hp⟩).2
      rw [←hvz] at hh
      change (t⁻¹*p*t)*v*(t⁻¹*p*t)⁻¹ = v
      calc
        _ = t⁻¹*(p*(t*v*t⁻¹)*p⁻¹)*t := by group
        _ = v := by rw [hh]; group
    have hh := hfirstzero b' ⟨v,hv⟩ (fun he => hv1 (congrArg Subtype.val he)) hb'pow hf
    have hex := source_natural_pair_conjugate D e ctx.nonnormal ht htn q hfirst hsecond b'
    have hb'b : originalOrbitConjugation ht b' = b := (originalOrbitConjugation ht).apply_symm_apply b
    rw [hb'b] at hex
    exact mem_map.mpr ⟨b,(congrArg Prod.snd hex).trans hh,rfl⟩
  · left
    intro p hp
    let b : R := ⟨p,hBR (hPB hp)⟩
    have hbpow : b ^ Nat.card P = 1 := Subtype.ext
      (congrArg (fun x : P => (x:G)) (pow_card_eq_one' (x := (⟨p,hp⟩ : P))))
    exact mem_map.mpr ⟨b,hfirstzero b ⟨w,hw⟩
      (fun he => hw1 (congrArg Subtype.val he)) hbpow (hPfix ⟨p,hp⟩).1,rfl⟩

end CFSG.Quasithin.Chapter10.MovingHall
