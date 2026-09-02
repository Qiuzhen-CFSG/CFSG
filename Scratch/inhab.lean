module
example (P : Prop) : P := by exact default
example (P : Prop) : Nonempty P := by infer_instance
