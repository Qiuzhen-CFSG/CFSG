module

public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FirstGenerator.OddIndex.SylowCandidate

/-!
# Literal matrix words for the candidate polycyclic sequence

Every word below lies in the specified matrix two-subgroup by construction.
The 21 selected words come from the straight-line derivation recorded in
`source/matrix-witness.json`; only nodes needed by the selected outputs are
retained. Their power-conjugate relations and generation of the whole subgroup
are separate proof obligations. Membership does not certify either assertion.

Source: the eleven existing max1 kernel generators and four certified Sylow
lifts in `SylowCandidate`. The untrusted discovery script, its original saved
input, and its word conventions are documented in `source/README.md`.
-/

@[expose] public section
namespace Janko4.LocalStructure.SylowNormalEights.MatrixWords

attribute [local irreducible] modelGroup matrixA matrixB

/-- The existing fifteen matrix generators, restricted to their own subgroup. -/
noncomputable def literalGenerator (i : Fin 11 ⊕ Fin 4) : OuterReduction.OddIndex.twoSubgroup :=
  ⟨OuterReduction.OddIndex.twoGenerator i, OuterReduction.OddIndex.twoGenerator_mem i⟩

/-- The specified fifteen words generate the entire intrinsic two-group. -/
theorem literalGenerator_closure : Subgroup.closure (Set.range literalGenerator) = ⊤ := by
  apply Subgroup.map_injective OuterReduction.OddIndex.twoSubgroup.subtype_injective
  rw [MonoidHom.map_closure, ← Set.range_comp, ← MonoidHom.range_eq_map,
    Subgroup.range_subtype]
  exact OuterReduction.OddIndex.twoSubgroup_eq_closure.symm

noncomputable def word0 : OuterReduction.OddIndex.twoSubgroup := 1
noncomputable def word1 : OuterReduction.OddIndex.twoSubgroup := literalGenerator (.inl 0)
noncomputable def word2 : OuterReduction.OddIndex.twoSubgroup := literalGenerator (.inl 1)
noncomputable def word3 : OuterReduction.OddIndex.twoSubgroup := literalGenerator (.inl 2)
noncomputable def word4 : OuterReduction.OddIndex.twoSubgroup := literalGenerator (.inl 3)
noncomputable def word5 : OuterReduction.OddIndex.twoSubgroup := literalGenerator (.inl 4)
noncomputable def word6 : OuterReduction.OddIndex.twoSubgroup := literalGenerator (.inl 5)
noncomputable def word7 : OuterReduction.OddIndex.twoSubgroup := literalGenerator (.inl 6)
noncomputable def word8 : OuterReduction.OddIndex.twoSubgroup := literalGenerator (.inl 7)
noncomputable def word9 : OuterReduction.OddIndex.twoSubgroup := literalGenerator (.inl 8)
noncomputable def word10 : OuterReduction.OddIndex.twoSubgroup := literalGenerator (.inl 9)
noncomputable def word11 : OuterReduction.OddIndex.twoSubgroup := literalGenerator (.inl 10)
noncomputable def word12 : OuterReduction.OddIndex.twoSubgroup := literalGenerator (.inr 0)
noncomputable def word13 : OuterReduction.OddIndex.twoSubgroup := literalGenerator (.inr 1)
noncomputable def word14 : OuterReduction.OddIndex.twoSubgroup := literalGenerator (.inr 2)
noncomputable def word15 : OuterReduction.OddIndex.twoSubgroup := literalGenerator (.inr 3)
noncomputable def word16 : OuterReduction.OddIndex.twoSubgroup := word15 * word15
noncomputable def word17 : OuterReduction.OddIndex.twoSubgroup := word14 * word16
noncomputable def word18 : OuterReduction.OddIndex.twoSubgroup := (word15)⁻¹
noncomputable def word19 : OuterReduction.OddIndex.twoSubgroup := (word17)⁻¹
noncomputable def word20 : OuterReduction.OddIndex.twoSubgroup := word18 * word19
noncomputable def word21 : OuterReduction.OddIndex.twoSubgroup := word15 * word17
noncomputable def word22 : OuterReduction.OddIndex.twoSubgroup := word20 * word21
noncomputable def word23 : OuterReduction.OddIndex.twoSubgroup := (word16)⁻¹
noncomputable def word24 : OuterReduction.OddIndex.twoSubgroup := (word17)⁻¹
noncomputable def word25 : OuterReduction.OddIndex.twoSubgroup := word23 * word24
noncomputable def word26 : OuterReduction.OddIndex.twoSubgroup := word16 * word17
noncomputable def word27 : OuterReduction.OddIndex.twoSubgroup := word25 * word26
noncomputable def word28 : OuterReduction.OddIndex.twoSubgroup := word17 * word17
noncomputable def word29 : OuterReduction.OddIndex.twoSubgroup := (word15)⁻¹
noncomputable def word30 : OuterReduction.OddIndex.twoSubgroup := (word28)⁻¹
noncomputable def word31 : OuterReduction.OddIndex.twoSubgroup := word29 * word30
noncomputable def word32 : OuterReduction.OddIndex.twoSubgroup := word15 * word28
noncomputable def word33 : OuterReduction.OddIndex.twoSubgroup := word31 * word32
noncomputable def word34 : OuterReduction.OddIndex.twoSubgroup := (word17)⁻¹
noncomputable def word35 : OuterReduction.OddIndex.twoSubgroup := (word33)⁻¹
noncomputable def word36 : OuterReduction.OddIndex.twoSubgroup := word34 * word35
noncomputable def word37 : OuterReduction.OddIndex.twoSubgroup := word17 * word33
noncomputable def word38 : OuterReduction.OddIndex.twoSubgroup := word36 * word37
noncomputable def word39 : OuterReduction.OddIndex.twoSubgroup := word27 * word28
noncomputable def word40 : OuterReduction.OddIndex.twoSubgroup := word39 * word33
noncomputable def word41 : OuterReduction.OddIndex.twoSubgroup := word40 * word38
noncomputable def word42 : OuterReduction.OddIndex.twoSubgroup := (word15)⁻¹
noncomputable def word43 : OuterReduction.OddIndex.twoSubgroup := (word41)⁻¹
noncomputable def word44 : OuterReduction.OddIndex.twoSubgroup := word42 * word43
noncomputable def word45 : OuterReduction.OddIndex.twoSubgroup := word15 * word41
noncomputable def word46 : OuterReduction.OddIndex.twoSubgroup := word44 * word45
noncomputable def word47 : OuterReduction.OddIndex.twoSubgroup := word46 * word38
noncomputable def word48 : OuterReduction.OddIndex.twoSubgroup := word22 * word16
noncomputable def word49 : OuterReduction.OddIndex.twoSubgroup := word48 * word47
noncomputable def word50 : OuterReduction.OddIndex.twoSubgroup := word13 * word16
noncomputable def word51 : OuterReduction.OddIndex.twoSubgroup := word50 * word28
noncomputable def word52 : OuterReduction.OddIndex.twoSubgroup := word51 * word47
noncomputable def word53 : OuterReduction.OddIndex.twoSubgroup := (word15)⁻¹
noncomputable def word54 : OuterReduction.OddIndex.twoSubgroup := (word52)⁻¹
noncomputable def word55 : OuterReduction.OddIndex.twoSubgroup := word53 * word54
noncomputable def word56 : OuterReduction.OddIndex.twoSubgroup := word15 * word52
noncomputable def word57 : OuterReduction.OddIndex.twoSubgroup := word55 * word56
noncomputable def word58 : OuterReduction.OddIndex.twoSubgroup := (word17)⁻¹
noncomputable def word59 : OuterReduction.OddIndex.twoSubgroup := (word52)⁻¹
noncomputable def word60 : OuterReduction.OddIndex.twoSubgroup := word58 * word59
noncomputable def word61 : OuterReduction.OddIndex.twoSubgroup := word17 * word52
noncomputable def word62 : OuterReduction.OddIndex.twoSubgroup := word60 * word61
noncomputable def word63 : OuterReduction.OddIndex.twoSubgroup := (word49)⁻¹
noncomputable def word64 : OuterReduction.OddIndex.twoSubgroup := (word52)⁻¹
noncomputable def word65 : OuterReduction.OddIndex.twoSubgroup := word63 * word64
noncomputable def word66 : OuterReduction.OddIndex.twoSubgroup := word49 * word52
noncomputable def word67 : OuterReduction.OddIndex.twoSubgroup := word65 * word66
noncomputable def word68 : OuterReduction.OddIndex.twoSubgroup := word67 * word38
noncomputable def word69 : OuterReduction.OddIndex.twoSubgroup := (word15)⁻¹
noncomputable def word70 : OuterReduction.OddIndex.twoSubgroup := (word68)⁻¹
noncomputable def word71 : OuterReduction.OddIndex.twoSubgroup := word69 * word70
noncomputable def word72 : OuterReduction.OddIndex.twoSubgroup := word15 * word68
noncomputable def word73 : OuterReduction.OddIndex.twoSubgroup := word71 * word72
noncomputable def word74 : OuterReduction.OddIndex.twoSubgroup := (word16)⁻¹
noncomputable def word75 : OuterReduction.OddIndex.twoSubgroup := (word68)⁻¹
noncomputable def word76 : OuterReduction.OddIndex.twoSubgroup := word74 * word75
noncomputable def word77 : OuterReduction.OddIndex.twoSubgroup := word16 * word68
noncomputable def word78 : OuterReduction.OddIndex.twoSubgroup := word76 * word77
noncomputable def word79 : OuterReduction.OddIndex.twoSubgroup := word78 * word33
noncomputable def word80 : OuterReduction.OddIndex.twoSubgroup := (word15)⁻¹
noncomputable def word81 : OuterReduction.OddIndex.twoSubgroup := (word79)⁻¹
noncomputable def word82 : OuterReduction.OddIndex.twoSubgroup := word80 * word81
noncomputable def word83 : OuterReduction.OddIndex.twoSubgroup := word15 * word79
noncomputable def word84 : OuterReduction.OddIndex.twoSubgroup := word82 * word83
noncomputable def word85 : OuterReduction.OddIndex.twoSubgroup := word84 * word38
noncomputable def word86 : OuterReduction.OddIndex.twoSubgroup := word73 * word28
noncomputable def word87 : OuterReduction.OddIndex.twoSubgroup := word86 * word47
noncomputable def word88 : OuterReduction.OddIndex.twoSubgroup := word87 * word33
noncomputable def word89 : OuterReduction.OddIndex.twoSubgroup := word88 * word38
noncomputable def word90 : OuterReduction.OddIndex.twoSubgroup := word62 * word16
noncomputable def word91 : OuterReduction.OddIndex.twoSubgroup := word90 * word47
noncomputable def word92 : OuterReduction.OddIndex.twoSubgroup := word91 * word33
noncomputable def word93 : OuterReduction.OddIndex.twoSubgroup := word92 * word85
noncomputable def word94 : OuterReduction.OddIndex.twoSubgroup := word93 * word38
noncomputable def word95 : OuterReduction.OddIndex.twoSubgroup := (word15)⁻¹
noncomputable def word96 : OuterReduction.OddIndex.twoSubgroup := (word94)⁻¹
noncomputable def word97 : OuterReduction.OddIndex.twoSubgroup := word95 * word96
noncomputable def word98 : OuterReduction.OddIndex.twoSubgroup := word15 * word94
noncomputable def word99 : OuterReduction.OddIndex.twoSubgroup := word97 * word98
noncomputable def word100 : OuterReduction.OddIndex.twoSubgroup := (word52)⁻¹
noncomputable def word101 : OuterReduction.OddIndex.twoSubgroup := (word94)⁻¹
noncomputable def word102 : OuterReduction.OddIndex.twoSubgroup := word100 * word101
noncomputable def word103 : OuterReduction.OddIndex.twoSubgroup := word52 * word94
noncomputable def word104 : OuterReduction.OddIndex.twoSubgroup := word102 * word103
noncomputable def word105 : OuterReduction.OddIndex.twoSubgroup := word104 * word28
noncomputable def word106 : OuterReduction.OddIndex.twoSubgroup := word105 * word47
noncomputable def word107 : OuterReduction.OddIndex.twoSubgroup := word106 * word79
noncomputable def word108 : OuterReduction.OddIndex.twoSubgroup := word99 * word16
noncomputable def word109 : OuterReduction.OddIndex.twoSubgroup := word108 * word47
noncomputable def word110 : OuterReduction.OddIndex.twoSubgroup := word109 * word85
noncomputable def word111 : OuterReduction.OddIndex.twoSubgroup := word110 * word38
noncomputable def word112 : OuterReduction.OddIndex.twoSubgroup := word57 * word107
noncomputable def word113 : OuterReduction.OddIndex.twoSubgroup := word112 * word68
noncomputable def word114 : OuterReduction.OddIndex.twoSubgroup := word113 * word79
noncomputable def word115 : OuterReduction.OddIndex.twoSubgroup := word114 * word85
noncomputable def word116 : OuterReduction.OddIndex.twoSubgroup := word12 * word94
noncomputable def word117 : OuterReduction.OddIndex.twoSubgroup := word116 * word107
noncomputable def word118 : OuterReduction.OddIndex.twoSubgroup := word117 * word111
noncomputable def word119 : OuterReduction.OddIndex.twoSubgroup := word118 * word89
noncomputable def word120 : OuterReduction.OddIndex.twoSubgroup := word119 * word33
noncomputable def word121 : OuterReduction.OddIndex.twoSubgroup := word120 * word85
noncomputable def word122 : OuterReduction.OddIndex.twoSubgroup := word121 * word38
noncomputable def word123 : OuterReduction.OddIndex.twoSubgroup := (word17)⁻¹
noncomputable def word124 : OuterReduction.OddIndex.twoSubgroup := (word122)⁻¹
noncomputable def word125 : OuterReduction.OddIndex.twoSubgroup := word123 * word124
noncomputable def word126 : OuterReduction.OddIndex.twoSubgroup := word17 * word122
noncomputable def word127 : OuterReduction.OddIndex.twoSubgroup := word125 * word126
noncomputable def word128 : OuterReduction.OddIndex.twoSubgroup := word127 * word107
noncomputable def word129 : OuterReduction.OddIndex.twoSubgroup := word128 * word111
noncomputable def word130 : OuterReduction.OddIndex.twoSubgroup := word129 * word89
noncomputable def word131 : OuterReduction.OddIndex.twoSubgroup := word130 * word47
noncomputable def word132 : OuterReduction.OddIndex.twoSubgroup := word131 * word33
noncomputable def word133 : OuterReduction.OddIndex.twoSubgroup := word132 * word79
noncomputable def word134 : OuterReduction.OddIndex.twoSubgroup := word133 * word38
noncomputable def word135 : OuterReduction.OddIndex.twoSubgroup := word10 * word17
noncomputable def word136 : OuterReduction.OddIndex.twoSubgroup := word135 * word94
noncomputable def word137 : OuterReduction.OddIndex.twoSubgroup := word136 * word16
noncomputable def word138 : OuterReduction.OddIndex.twoSubgroup := word137 * word49
noncomputable def word139 : OuterReduction.OddIndex.twoSubgroup := word138 * word68
noncomputable def word140 : OuterReduction.OddIndex.twoSubgroup := word139 * word41
noncomputable def word141 : OuterReduction.OddIndex.twoSubgroup := word140 * word28
noncomputable def word142 : OuterReduction.OddIndex.twoSubgroup := word141 * word47
noncomputable def word143 : OuterReduction.OddIndex.twoSubgroup := word142 * word85
noncomputable def word144 : OuterReduction.OddIndex.twoSubgroup := word143 * word38

/-- The marked 21 elements of the actual matrix group; indices match the presentation. -/
noncomputable def pcGenerator : Fin 21 → OuterReduction.OddIndex.twoSubgroup :=
  ![word17, word52, word15, word94, word115, word144, word16, word122, word49, word107, word68, word41, word134, word111, word28, word89, word47, word33, word79, word85, word38]

end Janko4.LocalStructure.SylowNormalEights.MatrixWords
