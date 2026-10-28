module
public import CFSG.Quasithin.Chapter2.Section04.SmallBlocks.AlternatingPair.Faithful
public import CFSG.Quasithin.Chapter2.Section04.SmallBlocks.AlternatingPair.Centralizer
public import CFSG.Quasithin.Chapter2.Section04.SmallBlocks.AlternatingPair.CubicActors
public import CFSG.Quasithin.Chapter2.Section04.SmallBlocks.AlternatingPair.Local

/-! The original paired block embeds faithfully in the actual two-core
quotient of G_I. A cubic in the other block survives there and centralizes
it. Generation by C-components places that faithful image in the layer.
These retain the literal quotient needed for source2.4.25, printed p542. -/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter2
open ChapterC ChapterC.Section05.ConjugateSource AlternatingFixedPhi
variable {G : Type*} [Group G] [Finite G] {M M₀ : Subgroup G} {d : MinimalBlockSetup M}

theorem AlternatingPairSourceSetup.phi_cubic_centralizer
    (c : AlternatingPairSourceSetup d M₀) :
    let S := (d.S : Subgroup d.H).map d.H.subtype
    let L := d.block.map d.H.subtype
    let GI := normalizer (Phi S L : Set G)
    ∃ b : GI, orderOf b = 3 ∧ b ∈ centralizer (L.subgroupOf GI : Set GI) := by
  obtain ⟨a,b,_,hb,_,hb3,_,_,_⟩ := c.cubic_actors
  have hbG : b ∈ normalizer (Phi ((d.S : Subgroup d.H).map d.H.subtype)
      (d.block.map d.H.subtype) : Set G) := Subgroup.centralizer_le_normalizer _
    (c.phi_intersection_centralized ⟨hb.1,c.join ▸ mem_sup_right hb.2⟩)
  refine ⟨⟨b,hbG⟩,(Subgroup.orderOf_coe ⟨b,hbG⟩).symm.trans hb3,?_⟩
  intro l hl
  exact Subtype.ext (c.commutes hb.2 l hl)

theorem AlternatingPairSourceSetup.phi_quotient_marks
    (c : AlternatingPairSourceSetup d M₀)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hu : ∀ N : Subgroup G, IsMaximalTwoLocal N → (T : Subgroup G) ≤ N → N = M)
    (hST : (d.S : Subgroup d.H).map d.H.subtype ≤ (T : Subgroup G))
    (hSM : (d.S : Subgroup d.H).map d.H.subtype ≤ M₀)
    (hMT : M₀ ≤ (T : Subgroup G))
    (hi : ((d.S : Subgroup d.H).map d.H.subtype).relIndex M₀ = 2) :
    let S := (d.S : Subgroup d.H).map d.H.subtype
    let L := d.block.map d.H.subtype
    let GI := normalizer (Phi S L : Set G)
    let B := (L.subgroupOf GI).map (QuotientGroup.mk' (pCore 2 GI))
    IsSQTK KnownSimple.IsKnownSimple (GI ⧸ pCore 2 GI) ∧
      Nonempty (L ≃* B) ∧ IsAlternatingBlock B 5 ∧
      B ≤ cComponentLayer (GI ⧸ pCore 2 GI) ∧
      ∃ b : GI ⧸ pCore 2 GI, orderOf b = 3 ∧ b ∈ centralizer (B : Set _) := by
  let S := (d.S : Subgroup d.H).map d.H.subtype
  let L := d.block.map d.H.subtype
  let GI := normalizer (Phi S L : Set G)
  let q := QuotientGroup.mk' (pCore 2 GI)
  let B := (L.subgroupOf GI).map q
  have henv := c.phi_normalizer_source hG T hM hTM hu hST hSM hMT hi
  have hLG : L ≤ GI := henv.2.2.2.1.trans (Subgroup.centralizer_le_normalizer _)
  let f : L →* GI ⧸ pCore 2 GI := q.comp (inclusion hLG)
  have hfi : Function.Injective f := by
    apply (MonoidHom.ker_eq_bot_iff f).mp
    apply eq_bot_iff.mpr
    intro l hl
    have hq : (inclusion hLG l) ∈ pCore 2 GI := (QuotientGroup.eq_one_iff _).mp hl
    have ha : (l : G) ∈ twoCore GI := mem_map_of_mem GI.subtype hq
    have h1 := (Subgroup.disjoint_def.mp c.block_disjoint_phi_core) l.property ha
    exact mem_bot.mpr (Subtype.ext h1)
  have hrange : f.range = B := by
    ext y
    constructor
    · rintro ⟨l,rfl⟩
      exact ⟨inclusion hLG l,l.property,rfl⟩
    · rintro ⟨l,hl,rfl⟩
      exact ⟨⟨l,hl⟩,rfl⟩
  let e : L ≃* B := (MonoidHom.ofInjective hfi).trans (MulEquiv.subgroupCongr hrange)
  have hA : IsAlternatingBlock B 5 := RankOne.Solvable.isAlternatingBlock_of_equiv e c.marked₁.block
  have hQ : IsSQTK KnownSimple.IsKnownSimple (GI ⧸ pCore 2 GI) :=
    Chapter1.Section02.uniqueness_local_quotient_sqtk hG henv.2.2.1.1
  have hLlocal := c.stabilizer_local_component
    (c.stabilizer_base hG T hM hTM hu hST hSM hMT hi).2.2.1
  let : Group.IsPerfect L := Chapter1.mem_L_isPerfect hLlocal
  let : Group.IsPerfect B := Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
  have hgen : cComponentLayer (GI ⧸ pCore 2 GI) = solvableResidual (GI ⧸ pCore 2 GI) :=
    ChapterA.Section03.SourceComponents.generation
      (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
      (ChapterA.Section03.SourceComponents.source_model_inputs_of_theoremC
        (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X)))
      hQ (pCore_quotient_pCore_eq_bot 2)
  refine ⟨hQ,⟨e⟩,hA,hgen ▸ le_solvableResidual_of_isPerfect B,?_⟩
  obtain ⟨b,hb,hbc⟩ := c.phi_cubic_centralizer
  have hbq : q b ≠ 1 := by
    intro he
    have hbp : b ∈ pCore 2 GI := (QuotientGroup.eq_one_iff _).mp he
    have hp : (⟨b,hbp⟩ : pCore 2 GI)^3=1 := Subtype.ext (hb ▸ pow_orderOf_eq_one b)
    have he1 : (⟨b,hbp⟩ : pCore 2 GI)=1 :=
      (pCore_isPGroup.powEquiv (by decide : Nat.Coprime 2 3)).injective (by
        simpa only [IsPGroup.powEquiv_apply,one_pow] using hp)
    have hb1 : b=1 := congrArg Subtype.val he1
    simp only [hb1,orderOf_one] at hb
    omega
  refine ⟨q b,?_,?_⟩
  · exact (Nat.dvd_prime (by decide : Nat.Prime 3)).mp
      (hb ▸ orderOf_map_dvd q b) |>.resolve_left (fun he => hbq (orderOf_eq_one_iff.mp he))
  · rintro y ⟨l,hl,rfl⟩
    exact congrArg q (hbc l hl)

end CFSG.Quasithin.Chapter2
